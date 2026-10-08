import OptCombinedSuspensionTaylor
import KLS.SuspensionTaylorNormalization
import KLS.LinearCumulantTaylor

/-! The single combined suspension direction also handles an unnormalized
smooth affine-orthogonal remainder and its full linear component. -/
open MeasureTheory Matrix Filter
open scoped ContDiff BigOperators ENNReal Topology
noncomputable section
namespace KLS
set_option maxHeartbeats 1000000

lemma Taylor_sum_le_of_universalCumulant_smoothAffine_combined {n d : ℕ} {V f : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure V)] (hV : ContDiff ℝ 2 V)
    (hμ : IsIsotropic (potentialMeasure V)) (hfs : SmoothAffineFunction f)
    (hf : MemLp f 2 (potentialMeasure V))
    (hmean : (∫ x, f x ∂potentialMeasure V) = 0)
    (hforth : ∀ j : Fin n, (∫ x, x j * f x ∂potentialMeasure V) = 0)
    {κ b : ℝ} (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian V x *ᵥ a))
    (hd : 0 < d) (hb : 0 ≤ b) (hglobal : UniversalDirectionalCumulantBound d b)
    (u : Space n) :
    (∑ a : Fin d → Fin n,
      exponentialTiltCoordinateTaylor V (fun x => f x + inner ℝ x u) d a ^ 2) ≤
      (b / (d.factorial : ℝ)^2) * (‖hf.toLp f‖^2 + ‖u‖^2) := by
  let r := ‖hf.toLp f‖
  by_cases hr : r = 0
  · have hz : hf.toLp f = 0 := norm_eq_zero.mp hr
    have he : f =ᵐ[potentialMeasure V] (fun _ => 0) :=
      hf.coeFn_toLp.symm.trans (hz ▸ Lp.coeFn_zero ℝ 2 (potentialMeasure V))
    have he' : (fun x => f x + inner ℝ x u) =ᵐ[potentialMeasure V]
        (fun x => inner ℝ x u) := by
      filter_upwards [he] with x hx
      simp only [hx, zero_add]
    simp_rw [exponentialTiltCoordinateTaylor_congr_ae he']
    simpa only [hz, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add] using
      Taylor_sum_le_of_universalCumulant_linear hV hμ hκ hlower hglobal u
  · let g : Space n → ℝ := fun x => r⁻¹ * f x
    have hg := hf.const_mul r⁻¹
    have hgs : SmoothAffineFunction g := hfs.const_mul r⁻¹
    have hgmean : (∫ x, g x ∂potentialMeasure V) = 0 := by
      simp only [g, integral_const_mul, hmean, mul_zero]
    have hgsq : (∫ x, (g x)^2 ∂potentialMeasure V) = 1 := by
      simp only [g, mul_pow, integral_const_mul]
      rw [← norm_toLp_sq_eq_integral_sq hf]
      change r⁻¹^2 * r^2 = 1
      field_simp
    have hgorth (j : Fin n) : (∫ x, x j * g x ∂potentialMeasure V) = 0 := by
      have he : (fun x : Space n => x j * g x) = fun x => r⁻¹ * (x j * f x) := by
        funext x
        dsimp [g]
        ring
      rw [he, integral_const_mul, hforth j, mul_zero]
    obtain ⟨M, hM⟩ := hgs.exists_hessian_bound
    obtain ⟨A, B, hAB⟩ := hgs.exists_linear_growth
    have hh := Taylor_sum_le_of_universalCumulant_normalized_combined hV hμ
      (hgs.contDiff.of_le (by simp)) hg hgmean hgsq hgorth hκ hlower hM hAB hd hb hglobal r u
    have he : (fun x => r*g x + inner ℝ x u) = (fun x => f x + inner ℝ x u) := by
      funext x
      dsimp [g]
      field_simp
    rwa [he] at hh

end KLS
end

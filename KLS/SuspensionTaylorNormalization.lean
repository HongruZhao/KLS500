import KLS.SmoothAffineFunctions
import KLS.SuspensionCumulantTaylorBound
import KLS.WeightedTaylorContinuity

/-! Removing the unit-variance restriction from the genuine suspension
estimate by normalizing the actual L2 norm. -/

open MeasureTheory Matrix Filter
open scoped ContDiff BigOperators ENNReal
noncomputable section
namespace KLS
set_option maxHeartbeats 1000000

lemma norm_toLp_sq_eq_integral_sq {n : ℕ} {μ : Measure (Space n)} {f : Space n → ℝ}
    (hf : MemLp f 2 μ) : ‖hf.toLp f‖ ^ 2 = ∫ x, (f x) ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  simp only [hx, RCLike.inner_apply, conj_trivial, pow_two]

lemma Taylor_sum_le_of_universalCumulant_smoothAffine {n d : ℕ} {V f : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure V)] (hV : ContDiff ℝ 2 V)
    (hμ : IsIsotropic (potentialMeasure V)) (hfs : SmoothAffineFunction f)
    (hf : MemLp f 2 (potentialMeasure V))
    (hmean : (∫ x, f x ∂potentialMeasure V) = 0)
    (hforth : ∀ j : Fin n, (∫ x, x j * f x ∂potentialMeasure V) = 0)
    {κ b : ℝ} (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian V x *ᵥ a))
    (hd : 0 < d) (hb : 0 ≤ b) (hglobal : UniversalDirectionalCumulantBound d b) :
    (∑ a : Fin d → Fin n, exponentialTiltCoordinateTaylor V f d a ^ 2) ≤
      (b / (d.factorial : ℝ) ^ 2) * ‖hf.toLp f‖ ^ 2 := by
  let r := ‖hf.toLp f‖
  by_cases hr : r = 0
  · have hz : hf.toLp f = 0 := norm_eq_zero.mp hr
    have he : f =ᵐ[potentialMeasure V] (fun _ => 0) :=
      hf.coeFn_toLp.symm.trans (hz ▸ Lp.coeFn_zero ℝ 2 (potentialMeasure V))
    have ht (a : Fin d → Fin n) : exponentialTiltCoordinateTaylor V f d a = 0 := by
      rw [exponentialTiltCoordinateTaylor_congr_ae he]
      exact exponentialTiltCoordinateTaylor_const hV hκ hlower 0 hd.ne' a
    simp only [ht, zero_pow (by norm_num : (2 : ℕ) ≠ 0), Finset.sum_const_zero]
    exact mul_nonneg (div_nonneg hb (sq_nonneg _)) (sq_nonneg _)
  · have hrpos : 0 < r := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hr)
    let g : Space n → ℝ := fun x => r⁻¹ * f x
    have hg := hf.const_mul r⁻¹
    have hgs : SmoothAffineFunction g := hfs.const_mul r⁻¹
    have hgmean : (∫ x, g x ∂potentialMeasure V) = 0 := by
      simp only [g, integral_const_mul, hmean, mul_zero]
    have hgsq : (∫ x, (g x) ^ 2 ∂potentialMeasure V) = 1 := by
      simp only [g, mul_pow, integral_const_mul]
      rw [← norm_toLp_sq_eq_integral_sq hf]
      change r⁻¹ ^ 2 * r ^ 2 = 1
      field_simp
    have hgorth (j : Fin n) : (∫ x, x j * g x ∂potentialMeasure V) = 0 := by
      have he : (fun x : Space n => x j * g x) = fun x => r⁻¹ * (x j * f x) := by
        funext x
        dsimp [g]
        ring
      rw [he, integral_const_mul, hforth j, mul_zero]
    obtain ⟨M, hM⟩ := hgs.exists_hessian_bound
    obtain ⟨A, B, hAB⟩ := hgs.exists_linear_growth
    have hh := Taylor_sum_le_of_universalCumulant_normalized hV hμ
      (hgs.contDiff.of_le (by simp)) hg hgmean hgsq hgorth hκ hlower hM hAB hd hb hglobal
    have he : (∑ a : Fin d → Fin n, exponentialTiltCoordinateTaylor V g d a ^ 2) =
        r⁻¹ ^ 2 * (∑ a : Fin d → Fin n, exponentialTiltCoordinateTaylor V f d a ^ 2) := by
      simp only [g, exponentialTiltCoordinateTaylor_const_mul hV hκ hlower hf, mul_pow,
        Finset.mul_sum]
    rw [he] at hh
    have hh' := mul_le_mul_of_nonneg_left hh (sq_nonneg r)
    have hc : r ^ 2 * (r⁻¹ ^ 2 *
        (∑ a : Fin d → Fin n, exponentialTiltCoordinateTaylor V f d a ^ 2)) =
        ∑ a : Fin d → Fin n, exponentialTiltCoordinateTaylor V f d a ^ 2 := by field_simp
    rw [hc] at hh'
    simpa only [r, mul_comm] using hh'

end KLS
end
#print axioms KLS.Taylor_sum_le_of_universalCumulant_smoothAffine

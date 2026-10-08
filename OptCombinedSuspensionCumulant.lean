import OptCombinedSuspensionDerivative
import KLS.WeightedTiltTaylorLinearity

/-! A single mixed cumulant now represents an orthogonal signal together
with its affine part, using the literal combined suspension direction. -/
open MeasureTheory Set Filter Matrix
open scoped ENNReal ContDiff Topology BigOperators
noncomputable section
namespace KLS
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {n N : ℕ} {V : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure V)]
  (hV : ContDiff ℝ 2 V) (hμ : IsIsotropic (potentialMeasure V)) {κ : ℝ} (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian V x *ᵥ a))

include hV hμ hκ hlower

lemma suspension_combined_derivative_on_block {f : Space n → ℝ}
    (hf : MemLp f 2 (potentialMeasure V)) (hfm : Measurable f) {A B : ℝ}
    (hbound : ∀ x, |f x| ≤ A + B * ‖x‖)
    (hmean : (∫ x, f x ∂potentialMeasure V) = 0)
    {β : ℝ} (hβ : 0 < β) {σ : ℝ} (hσ : σ ≠ 0) (ρ : ℝ) (u : Space n)
    (i : Fin N) (z : Space n) :
    fderiv ℝ (tiltLogLaplace (euclideanSuspensionLaw (N := N) (potentialMeasure V) f β σ (Real.sqrt N)⁻¹))
      (suspensionBlockEmbedding n N i z) (suspensionCombinedDirection n N (ρ*σ) u) =
        (Real.sqrt N)⁻¹ * ∫ x, (ρ*f x + inner ℝ x u) ∂exponentialTilt (potentialMeasure V) z := by
  have hExp : NormExponentialDomain (potentialMeasure V) (fun _ => 1) :=
    normExponentialDomain_of_memLp_potentialMeasure hV hκ hlower (memLp_const (1 : ℝ))
  rw [suspensionCombinedDirection_decomposition, map_add, map_smul, smul_eq_mul,
    suspension_noise_derivative_on_block hExp hfm hbound hmean hβ,
    suspension_pure_derivative_on_block hExp hμ hfm hbound hβ]
  rw [integral_add ((integrable_exponentialTilt_of_weighted_memLp hV hκ hlower hf z).const_mul ρ)
    (integrable_exponentialTilt_of_weighted_memLp hV hκ hlower (hμ.memLp_inner u) z), integral_const_mul]
  have hc : (ρ*σ) * ((Real.sqrt N)⁻¹ / σ) = ρ * (Real.sqrt N)⁻¹ := by
    calc
      _ = (ρ * (Real.sqrt N)⁻¹) * (σ * σ⁻¹) := by ring
      _ = _ := by rw [mul_inv_cancel₀ hσ, mul_one]
  rw [← mul_assoc, hc]
  ring

theorem cumulantTensor_suspension_combined_Taylor {d : ℕ} {f : Space n → ℝ}
    (hf : MemLp f 2 (potentialMeasure V)) (hfm : Measurable f) {A B : ℝ}
    (hbound : ∀ x, |f x| ≤ A + B * ‖x‖)
    (hmean : (∫ x, f x ∂potentialMeasure V) = 0)
    {β : ℝ} (hβ : 0 < β) {σ : ℝ} (hσ : σ ≠ 0) (hN : 0 < N)
    (ρ : ℝ) (u : Space n) (i : Fin N) (m : Fin d → Space n) :
    cumulantTensor (euclideanSuspensionLaw (N := N) (potentialMeasure V) f β σ (Real.sqrt N)⁻¹) (d+1)
      (Fin.snoc (fun j => suspensionBlockEmbedding n N i (m j))
        (suspensionCombinedDirection n N (ρ*σ) u)) =
      ((d.factorial : ℝ) / Real.sqrt N) *
        exponentialTiltTaylorCoefficient V (fun x => ρ*f x + inner ℝ x u) d m := by
  let G := tiltLogLaplace (euclideanSuspensionLaw (N := N) (potentialMeasure V) f β σ (Real.sqrt N)⁻¹)
  let L := suspensionBlockEmbedding n N i
  let F : Space n → ℝ := fun x => ρ*f x + inner ℝ x u
  have hExp : NormExponentialDomain (potentialMeasure V) (fun _ => 1) :=
    normExponentialDomain_of_memLp_potentialMeasure hV hκ hlower (memLp_const (1 : ℝ))
  have hs : ContDiffAt ℝ (d+1) G (L 0) := by
    simpa only [map_zero] using
      (contDiffAt_suspension_logLaplace hExp hfm hbound hβ σ (Real.sqrt N)⁻¹ 0 (map_zero _)).of_le (by simp)
  have hh := iteratedFDeriv_directional_comp L 0 (suspensionCombinedDirection n N (ρ*σ) u) hs m
  have he : (fun z => fderiv ℝ G (L z) (suspensionCombinedDirection n N (ρ*σ) u)) =
      (fun z => (Real.sqrt N)⁻¹ • (∫ x, F x ∂exponentialTilt (potentialMeasure V) z)) := by
    funext z
    exact suspension_combined_derivative_on_block hV hμ hκ hlower hf hfm hbound hmean hβ hσ ρ u i z
  rw [he] at hh
  have hF : ContDiffAt ℝ d (fun z => ∫ x, F x ∂exponentialTilt (potentialMeasure V) z) 0 :=
    (contDiff_exponentialTilt_average_of_weighted_memLp hV hκ hlower
      ((hf.const_mul ρ).add (hμ.memLp_inner u))).contDiffAt.of_le (by simp)
  rw [iteratedFDeriv_const_smul_apply' hF] at hh
  have ht : cumulantTensor (euclideanSuspensionLaw (N := N) (potentialMeasure V) f β σ (Real.sqrt N)⁻¹) (d+1)
      (Fin.snoc (fun j => suspensionBlockEmbedding n N i (m j))
        (suspensionCombinedDirection n N (ρ*σ) u)) =
      (Real.sqrt N)⁻¹ * iteratedFDeriv ℝ d (fun z => ∫ x, F x ∂exponentialTilt (potentialMeasure V) z) 0 m := by
    simpa only [_root_.smul_apply, smul_eq_mul, map_zero, cumulantTensor, G, L] using hh.symm
  rw [ht]
  unfold exponentialTiltTaylorCoefficient
  change (Real.sqrt N)⁻¹ * _ = ((d.factorial : ℝ) / Real.sqrt N) *
    (iteratedFDeriv ℝ d (fun z => ∫ x, F x ∂exponentialTilt (potentialMeasure V) z) 0 m / (d.factorial : ℝ))
  have hfac : (d.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero d)
  have hNs : Real.sqrt N ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hN)).ne'
  field_simp

end KLS
end

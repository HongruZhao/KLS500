import KLS.SuspensionBlockEmbedding
import KLS.LocalMixedFrechet
import KLS.WeightedTiltSymmetrizedTaylor
import KLS.TiltCumulantLowOrders

/-! Literal mixed cumulants of the suspension. The entries are derivatives
of its actual log-Laplace transform, and the base coefficients are derivatives
of the actual normalized exponential-tilt average. -/

open MeasureTheory
open scoped ENNReal ContDiff BigOperators
noncomputable section
namespace KLS

lemma suspension_noise_derivative_on_block {n N : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : NormExponentialDomain μ (fun _ => 1))
    {f : Space n → ℝ} (hf : Measurable f) {A B : ℝ}
    (hbound : ∀ x, |f x| ≤ A + B * ‖x‖) (hmean : (∫ x, f x ∂μ) = 0)
    {β : ℝ} (hβ : 0 < β) (σ c : ℝ) (i : Fin N) (z : Space n) :
    fderiv ℝ (tiltLogLaplace (euclideanSuspensionLaw (N := N) μ f β σ c))
      (suspensionBlockEmbedding n N i z) (suspensionNoiseDirection n N) =
        (c / σ) * ∫ x, f x ∂exponentialTilt μ z := by
  rw [fderiv_suspension_logLaplace_noise hμ hf hbound hβ σ c _
    (suspensionNoiseProjection_blockEmbedding n N i z)]
  congr 1
  rw [Finset.sum_eq_single i]
  · simp [suspensionCopyProjection_blockEmbedding]
  · intro j _ hj
    simp [suspensionCopyProjection_blockEmbedding, hj, hmean]
  · simp

theorem cumulantTensor_suspension_pure_block {n N d : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : NormExponentialDomain μ (fun _ => 1))
    {f : Space n → ℝ} (hf : Measurable f) {A B : ℝ}
    (hbound : ∀ x, |f x| ≤ A + B * ‖x‖) (hmean : (∫ x, f x ∂μ) = 0)
    {β : ℝ} (hβ : 0 < β) (σ c : ℝ) (i : Fin N) (m : Fin d → Space n) :
    cumulantTensor (euclideanSuspensionLaw (N := N) μ f β σ c) (d + 1)
      (Fin.snoc (fun j => suspensionBlockEmbedding n N i (m j))
        (suspensionNoiseDirection n N)) =
      (c / σ) * iteratedFDeriv ℝ d (fun z => ∫ x, f x ∂exponentialTilt μ z) 0 m := by
  let G := tiltLogLaplace (euclideanSuspensionLaw (N := N) μ f β σ c)
  let L := suspensionBlockEmbedding n N i
  have hs : ContDiffAt ℝ (d + 1) G (L 0) := by
    simpa only [map_zero] using
      (contDiffAt_suspension_logLaplace hμ hf hbound hβ σ c 0 (map_zero _)).of_le (by simp)
  have hh := iteratedFDeriv_directional_comp L 0 (suspensionNoiseDirection n N) hs m
  have he : (fun z => fderiv ℝ G (L z) (suspensionNoiseDirection n N)) =
      (fun z => (c / σ) • (∫ x, f x ∂exponentialTilt μ z)) := by
    funext z
    exact suspension_noise_derivative_on_block hμ hf hbound hmean hβ σ c i z
  rw [he] at hh
  have hF : ContDiffAt ℝ d (fun z => ∫ x, f x ∂exponentialTilt μ z) 0 :=
    (contDiff_exponentialTilt_average_of_linear_growth hμ hf hbound).contDiffAt.of_le (by simp)
  rw [iteratedFDeriv_const_smul_apply' hF] at hh
  simpa only [_root_.smul_apply, smul_eq_mul, map_zero, cumulantTensor, G, L] using hh.symm

theorem cumulantTensor_suspension_Taylor {n N d : ℕ} {V f : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure V)]
    (hμ : NormExponentialDomain (potentialMeasure V) (fun _ => 1))
    (hf : Measurable f) {A B : ℝ} (hbound : ∀ x, |f x| ≤ A + B * ‖x‖)
    (hmean : (∫ x, f x ∂potentialMeasure V) = 0) {β : ℝ} (hβ : 0 < β)
    (σ : ℝ) (i : Fin N) (m : Fin d → Space n) :
    cumulantTensor (euclideanSuspensionLaw (N := N) (potentialMeasure V) f β σ
      (Real.sqrt N)⁻¹) (d + 1)
      (Fin.snoc (fun j => suspensionBlockEmbedding n N i (m j))
        (suspensionNoiseDirection n N)) =
      ((d.factorial : ℝ) / (σ * Real.sqrt N)) * exponentialTiltTaylorCoefficient V f d m := by
  rw [cumulantTensor_suspension_pure_block hμ hf hbound hmean hβ]
  unfold exponentialTiltTaylorCoefficient
  have hfac : (d.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero d)
  field_simp [hfac]

end KLS
end
#print axioms KLS.cumulantTensor_suspension_pure_block
#print axioms KLS.cumulantTensor_suspension_Taylor

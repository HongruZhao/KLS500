import KLS.AdaptiveAverageGenerator

/-! Support bounds on a measurable test function give uniform bounds on its actual law average and noise. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS.AdaptiveLocalization
variable {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]
variable {f : Space n → ℝ} {B : ℝ}

theorem integrable_of_bounded_on_support (hf : Measurable f)
    (hB : ∀ x ∈ μ.support, |f x| ≤ B) : Integrable f μ := by
  apply Integrable.of_bound hf.aestronglyMeasurable B
  filter_upwards [μ.support_mem_ae] with x hx
  exact hB x hx

theorem ae_abs_le_law_of_support_bound (hμ : IsCompact μ.support)
    (hB : ∀ x ∈ μ.support, |f x| ≤ B) (p : Parameter n) :
    ∀ᵐ x ∂law μ p.1 p.2, |f x| ≤ B := by
  let := law_isProbability hμ p.1 p.2
  filter_upwards [(law μ p.1 p.2).support_mem_ae] with x hx
  exact hB x (by rwa [support_law hμ] at hx)

theorem abs_coordinateAverage_le (hμ : IsCompact μ.support)
    (hB : ∀ x ∈ μ.support, |f x| ≤ B) (z : Fin (n+n*n) → ℝ) :
    |coordinateAverage μ f z| ≤ B := by
  let := law_isProbability hμ (decodeState z).1 (decodeState z).2
  change ‖∫ x, f x ∂law μ (decodeState z).1 (decodeState z).2‖ ≤ B
  have hb : ∀ᵐ x ∂law μ (decodeState z).1 (decodeState z).2, ‖f x‖ ≤ B := by
    simpa only [Real.norm_eq_abs] using ae_abs_le_law_of_support_bound hμ hB (decodeState z)
  simpa using norm_integral_le_of_norm_le_const hb

def averageUniformNoiseBound (n : ℕ) (B : ℝ) : ℝ :=
  B * (isotropicTailRadius n * geometricNormMomentConstant 1)

theorem averageUniformNoiseBound_nonneg (n : ℕ) (hB0 : 0 ≤ B) :
    0 ≤ averageUniformNoiseBound n B :=
  mul_nonneg hB0 (mul_nonneg (isotropicTailRadius_pos n).le (geometricNormMomentConstant_pos 1).le)

theorem abs_averageNoiseCoefficient_le (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (hf : Measurable f) (hB0 : 0 ≤ B)
    (hB : ∀ x ∈ μ.support, |f x| ≤ B) (z : Fin (n+n*n) → ℝ)
    (hlc : measureLogConcave (law μ (decodeState z).1 (decodeState z).2)) (k : Fin n) :
    |averageNoiseCoefficient μ f k z| ≤ averageUniformNoiseBound n B := by
  let p := decodeState z
  let ν := law μ p.1 p.2
  let y := normalizedCenteredVector ν
  let : IsProbabilityMeasure ν := law_isProbability hμ p.1 p.2
  have hyint : Integrable (fun x => ‖y x‖) ν := by
    simpa only [pow_one] using hlc.integrable_normalizedCenteredVector_norm_pow 1
  have hyle : (∫ x, ‖y x‖ ∂ν) ≤ isotropicTailRadius n * geometricNormMomentConstant 1 := by
    have hp : (covarianceMatrix ν).PosDef := by
      rw [← covariance_eq_covarianceMatrix hμ p]
      exact covariance_posDef hμ hfull p
    simpa only [pow_one] using hlc.integral_normalizedCenteredVector_norm_pow_le hp 1
  rw [averageNoiseCoefficient_eq_integral hμ (integrable_of_bounded_on_support hf hB)]
  calc
    _ ≤ ∫ x, ‖f x * y x k‖ ∂ν := norm_integral_le_integral_norm _
    _ ≤ ∫ x, B*‖y x‖ ∂ν := by
      apply integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) (hyint.const_mul _)
      filter_upwards [ae_abs_le_law_of_support_bound hμ hB p] with x hx
      rw [norm_mul]
      exact mul_le_mul hx (PiLp.norm_apply_le (y x) k) (norm_nonneg _) hB0
    _ = B*(∫ x, ‖y x‖ ∂ν) := integral_const_mul _ _
    _ ≤ averageUniformNoiseBound n B := mul_le_mul_of_nonneg_left hyle hB0

end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.abs_averageNoiseCoefficient_le

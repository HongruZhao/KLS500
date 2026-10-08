import KLS.AdaptivePathLogConcavity
import KLS.NormalizedCenteredMoments

/-! Quantitative normalized centered moments along the actual localization path. -/
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped ENNReal BigOperators Topology Matrix.Norms.Elementwise
noncomputable section
namespace KLS.AdaptiveLocalization
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
open LevyStochCalc.Brownian.Ito KLS.LocalDiffusion KLSLevyProbe
universe u
variable {n : ℕ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {μ : Measure (Space n)} [IsProbabilityMeasure μ]
  {W : MultidimBrownianMotion P n} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ}
namespace MaximalProcess
variable (D : MaximalProcess μ W ℱ hW)

/-- A single event supports every order and every time before lifetime.
These quantitative constants depend only on dimension and order. -/
theorem ae_all_normalized_norm_moments (hμ : IsCompact μ.support) (hadm : admissibleMeasure μ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) < D.lifetime ω → ∀ p : ℕ,
      (∫ x, ‖normalizedCenteredVector (D.localizationLaw t ω) x‖^p ∂D.localizationLaw t ω) ≤
        isotropicTailRadius n ^ p * geometricNormMomentConstant p := by
  filter_upwards [D.ae_all_localizationLaw_logConcave hμ hadm] with ω hlc t ht hlife p
  letI := D.localizationLaw_isProbability hμ t ω
  have hp : (covarianceMatrix (D.localizationLaw t ω)).PosDef := by
    rw [D.covarianceMatrix_localizationLaw hμ]
    exact D.covariancePath_posDef hμ hadm.isotropic.affineSpan_support_eq_top t ω
  exact (hlc t ht hlife).integral_normalizedCenteredVector_norm_pow_le hp p

/-- The actual normalized coordinate products enjoy uniform finite-order bounds
along the process. Repeated coordinates and all finite orders are permitted. -/
theorem ae_all_normalized_coordinate_moments (hμ : IsCompact μ.support) (hadm : admissibleMeasure μ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) < D.lifetime ω →
      ∀ (p : ℕ) (r : Fin p → Fin n),
        |∫ x, ∏ a : Fin p, normalizedCenteredVector (D.localizationLaw t ω) x (r a)
          ∂D.localizationLaw t ω| ≤ isotropicTailRadius n ^ p * geometricNormMomentConstant p := by
  filter_upwards [D.ae_all_localizationLaw_logConcave hμ hadm] with ω hlc t ht hlife p r
  letI := D.localizationLaw_isProbability hμ t ω
  have hp : (covarianceMatrix (D.localizationLaw t ω)).PosDef := by
    rw [D.covarianceMatrix_localizationLaw hμ]
    exact D.covariancePath_posDef hμ hadm.isotropic.affineSpan_support_eq_top t ω
  exact (hlc t ht hlife).abs_integral_normalized_coordinate_prod_le hp r

end MaximalProcess
end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.MaximalProcess.ae_all_normalized_norm_moments
#print axioms KLS.AdaptiveLocalization.MaximalProcess.ae_all_normalized_coordinate_moments

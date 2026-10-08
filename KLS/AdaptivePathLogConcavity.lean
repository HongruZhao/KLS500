import KLS.AdaptiveExponentConcavity
import KLS.AdaptiveMaximalCovarianceIto

/-! Log-concavity of the actual normalized law before the constructed lifetime. -/
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix.Norms.Elementwise
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

def localizationLaw (t : ℝ) (ω : Ω) : Measure (Space n) :=
  law μ (D.parameterPath t ω).1 (D.parameterPath t ω).2

theorem localizationLaw_isProbability (hμ : IsCompact μ.support) (t : ℝ) (ω : Ω) :
    IsProbabilityMeasure (D.localizationLaw t ω) := law_isProbability hμ _ _

theorem support_localizationLaw (hμ : IsCompact μ.support) (t : ℝ) (ω : Ω) :
    (D.localizationLaw t ω).support = μ.support := support_law hμ _ _

theorem covarianceMatrix_localizationLaw (hμ : IsCompact μ.support) (t : ℝ) (ω : Ω) :
    covarianceMatrix (D.localizationLaw t ω) = D.covariancePath t ω :=
  (covariance_eq_covarianceMatrix hμ (D.parameterPath t ω)).symm

/-- Every actual localization law before lifetime is measure-log-concave on
one common event. The base density premise concerns only the original measure. -/
theorem ae_all_localizationLaw_logConcave_of_density (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (hd : HasLogConcaveDensity μ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) < D.lifetime ω →
      measureLogConcave (D.localizationLaw t ω) := by
  filter_upwards [D.ae_all_matrix_posSemidef hμ hfull] with ω hQ t ht hlife
  exact law_measureLogConcave_of_density hd _ (hQ t ht hlife)

/-- The literal compact-set isotropic base class supplies its own proved density
representation. Log-concavity of the evolving law is therefore a conclusion. -/
theorem ae_all_localizationLaw_logConcave (hμ : IsCompact μ.support) (hadm : admissibleMeasure μ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) < D.lifetime ω →
      measureLogConcave (D.localizationLaw t ω) :=
  D.ae_all_localizationLaw_logConcave_of_density hμ hadm.isotropic.affineSpan_support_eq_top
    hadm.hasLogConcaveDensity

end MaximalProcess
end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.MaximalProcess.ae_all_localizationLaw_logConcave

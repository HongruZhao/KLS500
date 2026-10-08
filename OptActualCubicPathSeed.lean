import OptCubicMatrixContraction
import KLS.AdaptiveMatrixSeedTransfer
import OptUniformCubicSeed

open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped Topology BigOperators Matrix.Norms.Elementwise
noncomputable section
namespace KLS.AdaptiveLocalization
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
open LevyStochCalc.Brownian.Ito KLS.LocalDiffusion KLSLevyProbe
variable {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

theorem covarianceNoise_cubic_seed_four
    (hμ : IsCompact μ.support) (hfull : affineSpan ℝ μ.support = ⊤)
    (z : Fin (n+n*n) → ℝ)
    (hlc : measureLogConcave (law μ (decodeState z).1 (decodeState z).2))
    (x : Space n) :
    ∑ k, (inner ℝ x ((whitenedCovarianceNoiseMatrix μ k z).toEuclideanLin x))^2 ≤
      4 * ‖x‖^4 := by
  let p := decodeState z
  let := law_isProbability hμ p.1 p.2
  have hp : (covarianceMatrix (law μ p.1 p.2)).PosDef := by
    rw [← covariance_eq_covarianceMatrix hμ]
    exact covariance_posDef hμ hfull p
  have hadm : admissibleMeasure (whitenedMeasure (law μ p.1 p.2)) :=
    ⟨inferInstance, hlc.whitenedMeasure, whitenedMeasure_isIsotropic hlc.memLp_id hp⟩
  have hcompact : IsCompact (whitenedMeasure (law μ p.1 p.2)).support := by
    apply isCompact_support_whitenedMeasure
    rwa [support_law hμ]
  simp_rw [whitenedCovarianceNoiseMatrix_eq_thirdCumulantMatrix hμ]
  exact ConstantReduction.admissible_thirdCumulantMatrix_cubic_seed_four hcompact hadm x

universe v
variable {Ω : Type v} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {W : MultidimBrownianMotion P n} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ}
namespace MaximalProcess
variable (D : MaximalProcess μ W ℱ hW)

theorem energyCubicSeed_unconditional
    (hμ : IsCompact μ.support) (hadm : admissibleMeasure μ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[ℱ 0] A) :
    D.EnergyCubicSeed := by
  filter_upwards [D.ae_all_localizationLaw_logConcave hμ hadm,
    D.ae_lifetime_eq_top hμ hadm hℱ0 hnull] with ω hlc htop t ht x hx
  have hlt : (t : WithTop ℝ) < D.lifetime ω := by
    rw [htop]
    exact WithTop.coe_lt_top t
  have hh := covarianceNoise_cubic_seed_four hμ hadm.isotropic.affineSpan_support_eq_top
    (D.path t ω) (hlc t ht hlt) x
  simpa only [hx,one_pow,mul_one] using hh

end MaximalProcess

theorem uniformCompactCubicSeed_unconditional (n : ℕ) : UniformCompactCubicSeed n := by
  intro μ inst hμ hadm Ω mΩ P instP W D
  exact D.energyCubicSeed_unconditional hμ hadm
    (usualFiltration_beforeZero W) (usualFiltration_null W)

end KLS.AdaptiveLocalization
end

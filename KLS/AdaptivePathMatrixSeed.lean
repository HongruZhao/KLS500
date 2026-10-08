import KLS.AdaptiveMatrixSeedTransfer

/-! A universal full quadratic bound produces the actual-path matrix seed
on the already established common event of log-concavity and nonexplosion. -/
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped NNReal ENNReal Topology BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS.AdaptiveLocalization
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
open LevyStochCalc.Brownian.Ito KLS.LocalDiffusion KLSLevyProbe
universe v
variable {n : ℕ} {Ω : Type v} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {μ : Measure (Space n)} [IsProbabilityMeasure μ]
  {W : MultidimBrownianMotion P n} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ}
namespace MaximalProcess
variable (D : MaximalProcess μ W ℱ hW)

/-- The remaining universal input is precisely the full quadratic-variance
bound on the original admissible class. The process seed is a conclusion. -/
theorem energyMatrixSeed_of_universal_quadratic
    (hμ : IsCompact μ.support) (hadm : admissibleMeasure μ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[ℱ 0] A)
    (hQ : ∀ ν : Measure (Space n), admissibleMeasure ν → QuadraticVarianceEight ν) :
    D.EnergyMatrixSeed := by
  filter_upwards [D.ae_all_localizationLaw_logConcave hμ hadm,
    D.ae_lifetime_eq_top hμ hadm hℱ0 hnull] with ω hlc htop t ht
  have hlt : (t : WithTop ℝ) < D.lifetime ω := by
    rw [htop]
    exact WithTop.coe_lt_top t
  exact covarianceNoise_seed_eight_of_universal_quadratic hμ hadm.isotropic.affineSpan_support_eq_top
    (D.path t ω) (hlc t ht hlt) hQ

end MaximalProcess
end KLS.AdaptiveLocalization
end

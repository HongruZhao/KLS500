import KLS.IntegratedEnergyFinite

open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped Topology BigOperators Matrix.Norms.Elementwise
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

def EnergyCubicSeed (D : MaximalProcess μ W ℱ hW) : Prop :=
  ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ x : Space n, ‖x‖ = 1 →
    ∑ k, (inner ℝ x ((whitenedCovarianceNoiseMatrix μ k (D.path t ω)).toEuclideanLin x))^2 ≤ 4

end MaximalProcess
end KLS.AdaptiveLocalization
end

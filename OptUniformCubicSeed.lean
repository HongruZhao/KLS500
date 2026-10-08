import OptEnergyCubicSeed
import KLS.CompactEnergyInduction

open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped Topology BigOperators Matrix.Norms.Elementwise
noncomputable section
namespace KLS.AdaptiveLocalization
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
open LevyStochCalc.Brownian.Ito KLS.LocalDiffusion KLSLevyProbe

def UniformCompactCubicSeed (n : ℕ) : Prop :=
  ∀ (μ : Measure (Space n)) [IsProbabilityMeasure μ], IsCompact μ.support → admissibleMeasure μ →
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (W : MultidimBrownianMotion P n)
      (D : MaximalProcess μ W (usualFiltration W) (usualFiltration_brownian W)),
      D.EnergyCubicSeed

end KLS.AdaptiveLocalization
end

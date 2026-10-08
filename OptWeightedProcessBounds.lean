import KLS.QuadraticEightFullPoincare

/-! Explicit weighted process predicates used by the genuine energy induction. -/
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped NNReal ENNReal Topology BigOperators Matrix.Norms.Elementwise
noncomputable section
namespace KLS.AdaptiveLocalization
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
open LevyStochCalc.Brownian.Ito KLS.LocalDiffusion KLSLevyProbe

def CompactProcessWeightedEnergyBound (n r : ℕ) (B θ : ℝ) : Prop :=
  ∀ (μ : Measure (Space n)) [IsProbabilityMeasure μ], IsCompact μ.support → admissibleMeasure μ →
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (W : MultidimBrownianMotion P n)
      (D : MaximalProcess μ W (usualFiltration W) (usualFiltration_brownian W)) (u : Space n),
      cumulantEnergy μ r u 0 + θ * D.integratedEnergy (r+1) u ≤ B * ‖u‖^2

def CompactProcessScaledIntegratedEnergyBound (n r : ℕ) (B β : ℝ) : Prop :=
  ∀ (μ : Measure (Space n)) [IsProbabilityMeasure μ], IsCompact μ.support → admissibleMeasure μ →
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (W : MultidimBrownianMotion P n)
      (D : MaximalProcess μ W (usualFiltration W) (usualFiltration_brownian W)) (u : Space n),
      D.integratedEnergy (r+1) u ≤ β * B * ‖u‖^2

theorem compactCumulantEnergyBound_of_weightedProcessBound {n r : ℕ} {B θ : ℝ}
    (hθ : 0 ≤ θ) (hB : CompactProcessWeightedEnergyBound n r B θ) :
    CompactCumulantEnergyBound n r B := by
  intro μ hμ hadm u
  let := hadm.isProb
  obtain ⟨Ω, mΩ, P, hP, W, D, _⟩ := exists_adaptiveGlobalProcess μ hμ hadm
  let := mΩ
  let := hP
  have hh := hB μ hμ hadm Ω P W D u
  have hn := D.integratedEnergy_nonnegative hμ hadm (r+1) u
  rw [cumulantEnergy_zero hadm.isotropic r u] at hh
  simp only [cumulantSliceDirections] at hh
  linarith [mul_nonneg hθ hn]

end KLS.AdaptiveLocalization
end

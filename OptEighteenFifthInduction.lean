import OptEighteenFifthStep

set_option maxRecDepth 8192

/-! The genuine compact and integrated energy bounds hold at every rank. -/
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped NNReal ENNReal Topology BigOperators Matrix.Norms.Elementwise
noncomputable section
namespace KLS.AdaptiveLocalization
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
open LevyStochCalc.Brownian.Ito KLS.LocalDiffusion KLSLevyProbe

theorem compactCumulantAndIntegratedEnergyBound_eighteenFifth {n : ℕ}
    (hseed : UniformCompactMatrixSeed n) (hcubic : UniformCompactCubicSeed n) : ∀ r, 1 ≤ r →
    CompactCumulantEnergyBound n r
      ((63/500 : ℝ)*eighteenFifthCumulantWeight r*cumulantEnergyMajorant (91/5) r) ∧
    CompactProcessScaledIntegratedEnergyBound n r
      ((9/20 : ℝ)*eighteenFifthIntegralWeight r*cumulantEnergyMajorant (91/5) r) 1 := by
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro hr
    by_cases hsmall : r ≤ 128
    · exact compactCumulantAndIntegratedEnergyBound_eighteenFifth_base hseed hcubic hr hsmall
    have hr129 : 129 ≤ r := by omega
    constructor
    · apply compactCumulantEnergyBound_of_weightedProcessBound (θ := 0) (by norm_num)
      intro μ inst hμ hadm Ω mΩ P instP W D u
      have hh := D.eighteenFifth_energy_induction_step hμ hadm
        (usualFiltration_beforeZero W) (usualFiltration_null W) hr129 u
        (hseed μ hμ hadm Ω P W D) (hcubic μ hμ hadm Ω P W D)
        (fun j hj hlt => (ih j hlt hj).1)
        (fun j hj hlt => by simpa only [one_mul] using (ih j hlt hj).2 μ hμ hadm Ω P W D u)
      simpa only [zero_mul, add_zero] using hh.1
    · intro μ inst hμ hadm Ω mΩ P instP W D u
      have hh := D.eighteenFifth_energy_induction_step hμ hadm
        (usualFiltration_beforeZero W) (usualFiltration_null W) hr129 u
        (hseed μ hμ hadm Ω P W D) (hcubic μ hμ hadm Ω P W D)
        (fun j hj hlt => (ih j hlt hj).1)
        (fun j hj hlt => by simpa only [one_mul] using (ih j hlt hj).2 μ hμ hadm Ω P W D u)
      simpa only [one_mul] using hh.2

end KLS.AdaptiveLocalization
end

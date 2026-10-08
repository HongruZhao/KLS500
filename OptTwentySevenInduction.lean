import OptTwentySevenStep

/-! The genuine compact and integrated energy bounds hold at every rank. -/
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped NNReal ENNReal Topology BigOperators Matrix.Norms.Elementwise
noncomputable section
namespace KLS.AdaptiveLocalization
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
open LevyStochCalc.Brownian.Ito KLS.LocalDiffusion KLSLevyProbe

theorem compactCumulantAndIntegratedEnergyBound_twentySeven {n : ℕ}
    (hseed : UniformCompactMatrixSeed n) : ∀ r, 1 ≤ r →
    CompactCumulantEnergyBound n r
      ((43/2000 : ℝ)*twentySevenCumulantWeight r*cumulantEnergyMajorant (27) r) ∧
    CompactProcessScaledIntegratedEnergyBound n r
      ((13/125 : ℝ)*twentySevenIntegralWeight r*cumulantEnergyMajorant (27) r) 1 := by
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro hr
    by_cases hsmall : r ≤ 16
    · exact compactCumulantAndIntegratedEnergyBound_twentySeven_base hseed hr hsmall
    have hr17 : 17 ≤ r := by omega
    constructor
    · apply compactCumulantEnergyBound_of_weightedProcessBound (θ := 0) (by norm_num)
      intro μ inst hμ hadm Ω mΩ P instP W D u
      have hh := D.twentySeven_energy_induction_step hμ hadm
        (usualFiltration_beforeZero W) (usualFiltration_null W) hr17 u
        (hseed μ hμ hadm Ω P W D)
        (fun j hj hlt => (ih j hlt hj).1)
        (fun j hj hlt => by simpa only [one_mul] using (ih j hlt hj).2 μ hμ hadm Ω P W D u)
      simpa only [zero_mul, add_zero] using hh.1
    · intro μ inst hμ hadm Ω mΩ P instP W D u
      have hh := D.twentySeven_energy_induction_step hμ hadm
        (usualFiltration_beforeZero W) (usualFiltration_null W) hr17 u
        (hseed μ hμ hadm Ω P W D)
        (fun j hj hlt => (ih j hlt hj).1)
        (fun j hj hlt => by simpa only [one_mul] using (ih j hlt hj).2 μ hμ hadm Ω P W D u)
      simpa only [one_mul] using hh.2

end KLS.AdaptiveLocalization
end

import OptRankYoungStep

/-! Every compact cumulant and integrated energy through rank sixteen
is established by strong induction from the exact first two ranks. -/
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped NNReal ENNReal Topology BigOperators Matrix.Norms.Elementwise
noncomputable section
namespace KLS.AdaptiveLocalization
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
open LevyStochCalc.Brownian.Ito KLS.LocalDiffusion KLSLevyProbe

theorem compactCumulantAndIntegratedEnergyBound_rankYoung {n : ℕ}
    (hseed : UniformCompactMatrixSeed n) : ∀ r, 1 ≤ r → r ≤ 16 →
      CompactCumulantEnergyBound n r (rankYoungCumulantWeight r * cumulantEnergyMajorant 1 r) ∧
      CompactProcessScaledIntegratedEnergyBound n r
        (rankYoungIntegralWeight r * cumulantEnergyMajorant 1 r) 1 := by
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro hr hr16
    by_cases h1 : r = 1
    · subst r
      norm_num [cumulantEnergyMajorant]
      exact ⟨compactCumulantEnergyBound_one_exact, finiteRank_integral_two_bound hseed⟩
    have hr2 : 2 ≤ r := by omega
    constructor
    · by_cases h2 : r = 2
      · subst r
        norm_num [cumulantEnergyMajorant]
        exact compactCumulantEnergyBound_two_eight_unconditional
      · have hr3 : 3 ≤ r := by omega
        apply compactCumulantEnergyBound_of_weightedProcessBound (θ := 0) (by norm_num)
        intro μ inst hμ hadm Ω mΩ P instP W D u
        have hh := D.rankYoung_energy_induction_step hμ hadm
          (usualFiltration_beforeZero W) (usualFiltration_null W) hr2 hr16 u
          (hseed μ hμ hadm Ω P W D)
          (fun j hj hlt => (ih j hlt hj (by omega)).1)
          (fun j hj hlt => by
            simpa only [one_mul] using (ih j hlt hj (by omega)).2 μ hμ hadm Ω P W D u)
        simpa only [zero_mul, add_zero] using hh.1 hr3
    · intro μ inst hμ hadm Ω mΩ P instP W D u
      have hh := D.rankYoung_energy_induction_step hμ hadm
        (usualFiltration_beforeZero W) (usualFiltration_null W) hr2 hr16 u
        (hseed μ hμ hadm Ω P W D)
        (fun j hj hlt => (ih j hlt hj (by omega)).1)
        (fun j hj hlt => by
          simpa only [one_mul] using (ih j hlt hj (by omega)).2 μ hμ hadm Ω P W D u)
      simpa only [one_mul] using hh.2

end KLS.AdaptiveLocalization
end

import OptCumulantTwentyEightHalfStep
import OptWeightedProcessBounds
import OptCumulantRankTwo

/-! Separate compact and integrated envelopes preserve the genuine rank-two
quadratic estimate while closing the actual localization energy induction. -/
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped NNReal ENNReal Topology BigOperators Matrix.Norms.Elementwise
noncomputable section
namespace KLS.AdaptiveLocalization
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
open LevyStochCalc.Brownian.Ito KLS.LocalDiffusion KLSLevyProbe

theorem compactCumulantEnergyBound_one_twentyEightHalf {n : ℕ} :
    CompactCumulantEnergyBound n 1
      ((43/1000 : ℝ) * twentyEightHalfCumulantWeight 1 * cumulantEnergyMajorant (57/2) 1) := by
  intro μ hμ hadm u
  let := hadm.isProb
  have hh := cumulantEnergy_one_zero hμ hadm.isotropic u
  rw [cumulantEnergy_zero hadm.isotropic 1 u] at hh
  simp only [cumulantSliceDirections] at hh
  norm_num [cumulantEnergyMajorant, twentyEightHalfCumulantWeight]
  rw [hh]
  nlinarith [sq_nonneg ‖u‖]

theorem compactProcessIntegratedEnergyBound_one_twentyEightHalf {n : ℕ}
    (hseed : UniformCompactMatrixSeed n) :
    CompactProcessScaledIntegratedEnergyBound n 1
      ((43/1000 : ℝ) * twentyEightHalfIntegralWeight 1 * cumulantEnergyMajorant (57/2) 1) (7/3) := by
  intro μ inst hμ hadm Ω mΩ P instP W D u
  have hh := D.integratedEnergy_two_le_eight hμ hadm
    (usualFiltration_beforeZero W) (usualFiltration_null W) u (hseed μ hμ hadm Ω P W D)
  norm_num [cumulantEnergyMajorant, twentyEightHalfIntegralWeight] at ⊢
  exact hh

theorem compactCumulantEnergyBound_two_twentyEightHalf {n : ℕ} :
    CompactCumulantEnergyBound n 2
      ((43/1000 : ℝ) * twentyEightHalfCumulantWeight 2 * cumulantEnergyMajorant (57/2) 2) := by
  norm_num [twentyEightHalfCumulantWeight, cumulantEnergyMajorant]
  exact compactCumulantEnergyBound_two_eight_unconditional

theorem compactCumulantAndIntegratedEnergyBound_twentyEightHalf {n : ℕ}
    (hseed : UniformCompactMatrixSeed n) :
    ∀ r, 1 ≤ r →
      CompactCumulantEnergyBound n r
        ((43/1000 : ℝ) * twentyEightHalfCumulantWeight r * cumulantEnergyMajorant (57/2) r) ∧
      CompactProcessScaledIntegratedEnergyBound n r
        ((43/1000 : ℝ) * twentyEightHalfIntegralWeight r * cumulantEnergyMajorant (57/2) r) (7/3) := by
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro hr
    by_cases h1 : r = 1
    · subst r
      exact ⟨compactCumulantEnergyBound_one_twentyEightHalf,
        compactProcessIntegratedEnergyBound_one_twentyEightHalf hseed⟩
    have hr2 : 2 ≤ r := by omega
    have hcombined : CompactProcessWeightedEnergyBound n r
        ((43/1000 : ℝ) * twentyEightHalfIntegralWeight r * cumulantEnergyMajorant (57/2) r) (3/7) := by
      intro μ inst hμ hadm Ω mΩ P instP W D u
      apply D.compact_energy_induction_step_twentyEightHalf hμ hadm
        (usualFiltration_beforeZero W) (usualFiltration_null W) hr2 u
        (hseed μ hμ hadm Ω P W D)
      · intro j hj hlt
        exact (ih j hlt hj).1
      · intro j hj hlt
        exact (ih j hlt hj).2 μ hμ hadm Ω P W D u
    constructor
    · by_cases h2 : r = 2
      · subst r
        exact compactCumulantEnergyBound_two_twentyEightHalf
      · rw [twentyEightHalfCumulantWeight_eq_integral (by omega : 3 ≤ r)]
        exact compactCumulantEnergyBound_of_weightedProcessBound (by norm_num) hcombined
    · intro μ inst hμ hadm Ω mΩ P instP W D u
      have hh := hcombined μ hμ hadm Ω P W D u
      have hn := cumulantEnergy_nonnegative (r := r) hμ hadm.isotropic.affineSpan_support_eq_top u 0
      linarith

end KLS.AdaptiveLocalization
end

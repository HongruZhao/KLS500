import OptCumulantTwentyNineStep
import KLS.QuadraticEightFullPoincare

/-! The separate rank-one estimates match the changed three-sevenths
coercive coefficient; every later combined estimate is proved inductively. -/
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped NNReal ENNReal Topology BigOperators Matrix.Norms.Elementwise
noncomputable section
namespace KLS.AdaptiveLocalization
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
open LevyStochCalc.Brownian.Ito KLS.LocalDiffusion KLSLevyProbe

def CompactProcessThreeSeventhsEnergyBound (n r : ℕ) (B : ℝ) : Prop :=
  ∀ (μ : Measure (Space n)) [IsProbabilityMeasure μ], IsCompact μ.support → admissibleMeasure μ →
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (W : MultidimBrownianMotion P n)
      (D : MaximalProcess μ W (usualFiltration W) (usualFiltration_brownian W)) (u : Space n),
      cumulantEnergy μ r u 0 + (3/7 : ℝ) * D.integratedEnergy (r+1) u ≤ B * ‖u‖^2

def CompactProcessSevenThirdsIntegratedEnergyBound (n r : ℕ) (B : ℝ) : Prop :=
  ∀ (μ : Measure (Space n)) [IsProbabilityMeasure μ], IsCompact μ.support → admissibleMeasure μ →
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (W : MultidimBrownianMotion P n)
      (D : MaximalProcess μ W (usualFiltration W) (usualFiltration_brownian W)) (u : Space n),
      D.integratedEnergy (r+1) u ≤ (7/3 : ℝ) * B * ‖u‖^2

theorem compactCumulantEnergyBound_of_threeSeventhsProcessBound {n r : ℕ} {B : ℝ}
    (hB : CompactProcessThreeSeventhsEnergyBound n r B) : CompactCumulantEnergyBound n r B := by
  intro μ hμ hadm u
  let := hadm.isProb
  obtain ⟨Ω, mΩ, P, hP, W, D, _⟩ := exists_adaptiveGlobalProcess μ hμ hadm
  let := mΩ
  let := hP
  have hh := hB μ hμ hadm Ω P W D u
  have hn := D.integratedEnergy_nonnegative hμ hadm (r+1) u
  rw [cumulantEnergy_zero hadm.isotropic r u] at hh
  simp only [cumulantSliceDirections] at hh
  linarith

theorem compactCumulantEnergyBound_one_twentyNine {n : ℕ} :
    CompactCumulantEnergyBound n 1 ((1/20 : ℝ) * twentyNineRankWeight 1 * cumulantEnergyMajorant 29 1) := by
  intro μ hμ hadm u
  let := hadm.isProb
  have hh := cumulantEnergy_one_zero hμ hadm.isotropic u
  rw [cumulantEnergy_zero hadm.isotropic 1 u] at hh
  simp only [cumulantSliceDirections] at hh
  norm_num [cumulantEnergyMajorant, twentyNineRankWeight]
  rw [hh]
  nlinarith [sq_nonneg ‖u‖]

theorem compactProcessIntegratedEnergyBound_one_twentyNine {n : ℕ}
    (hseed : UniformCompactMatrixSeed n) :
    CompactProcessSevenThirdsIntegratedEnergyBound n 1
      ((1/20 : ℝ) * twentyNineRankWeight 1 * cumulantEnergyMajorant 29 1) := by
  intro μ inst hμ hadm Ω mΩ P instP W D u
  have hh := D.integratedEnergy_two_le_eight hμ hadm
    (usualFiltration_beforeZero W) (usualFiltration_null W) u (hseed μ hμ hadm Ω P W D)
  norm_num [cumulantEnergyMajorant, twentyNineRankWeight] at ⊢
  exact hh

theorem compactCumulantAndIntegratedEnergyBound_twentyNine {n : ℕ}
    (hseed : UniformCompactMatrixSeed n) :
    ∀ r, 1 ≤ r →
      CompactCumulantEnergyBound n r ((1/20 : ℝ) * twentyNineRankWeight r * cumulantEnergyMajorant 29 r) ∧
      CompactProcessSevenThirdsIntegratedEnergyBound n r
        ((1/20 : ℝ) * twentyNineRankWeight r * cumulantEnergyMajorant 29 r) := by
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro hr
    by_cases h1 : r = 1
    · subst r
      exact ⟨compactCumulantEnergyBound_one_twentyNine, compactProcessIntegratedEnergyBound_one_twentyNine hseed⟩
    have hr2 : 2 ≤ r := by omega
    have hcombined : CompactProcessThreeSeventhsEnergyBound n r
        ((1/20 : ℝ) * twentyNineRankWeight r * cumulantEnergyMajorant 29 r) := by
      intro μ inst hμ hadm Ω mΩ P instP W D u
      apply D.compact_energy_induction_step_twentyNine hμ hadm
        (usualFiltration_beforeZero W) (usualFiltration_null W) hr2 u
        (hseed μ hμ hadm Ω P W D)
      · intro j hj hlt
        exact (ih j hlt hj).1
      · intro j hj hlt
        exact (ih j hlt hj).2 μ hμ hadm Ω P W D u
    refine ⟨compactCumulantEnergyBound_of_threeSeventhsProcessBound hcombined, ?_⟩
    intro μ inst hμ hadm Ω mΩ P instP W D u
    have hh := hcombined μ hμ hadm Ω P W D u
    have hn := cumulantEnergy_nonnegative (r := r) hμ hadm.isotropic.affineSpan_support_eq_top u 0
    linarith

end KLS.AdaptiveLocalization
end

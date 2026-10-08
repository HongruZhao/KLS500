import OptZeroCoercivityEnergyInfinite
import OptThreeSeventhsEnergyInfinite
import OptMixedLowerIntegral
import OptWeightedProcessBounds
import OptCumulantRankTwo

/-! A direct finite-rank chain preserves the exact rank-one and rank-two
estimates and uses zero coercivity for the compact cumulant envelope. -/
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped NNReal ENNReal Topology BigOperators Matrix.Norms.Elementwise
noncomputable section
namespace KLS

def finiteRankCumulantWeight (r : ℕ) : ℝ :=
  if r = 1 then 1 else if r = 2 then 2 else if r = 3 then 576 else 1

def finiteRankIntegralWeight (r : ℕ) : ℝ :=
  if r = 1 then 8 else if r = 2 then 168 else if r = 3 then 3696 else 1

theorem finiteRankCumulantWeight_nonneg (r : ℕ) : 0 ≤ finiteRankCumulantWeight r := by
  unfold finiteRankCumulantWeight
  split_ifs <;> norm_num

namespace RouteArithmetic

theorem sqrt_product_le_of_scaled_bounds {e l s A B H : ℝ}
    (he0 : 0 ≤ e) (hl0 : 0 ≤ l) (hs : 0 ≤ s) (hA : 0 ≤ A) (hH : 0 ≤ H)
    (he : e ≤ A*s) (hl : l ≤ B*s) (hAB : A*B ≤ H^2) :
    Real.sqrt e * Real.sqrt l ≤ H*s := by
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt he0, Real.sq_sqrt hl0]
  calc
    e*l ≤ (A*s)*(B*s) := mul_le_mul he hl hl0 (mul_nonneg hA hs)
    _ = (A*B)*s^2 := by ring
    _ ≤ H^2*s^2 := mul_le_mul_of_nonneg_right hAB (sq_nonneg s)
    _ = (H*s)^2 := by ring

end RouteArithmetic
namespace AdaptiveLocalization
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
open LevyStochCalc.Brownian.Ito KLS.LocalDiffusion KLSLevyProbe

theorem compactCumulantEnergyBound_one_exact {n : ℕ} :
    CompactCumulantEnergyBound n 1 1 := by
  intro μ hμ hadm u
  let := hadm.isProb
  have hh := cumulantEnergy_one_zero hμ hadm.isotropic u
  rw [cumulantEnergy_zero hadm.isotropic 1 u] at hh
  simpa only [cumulantSliceDirections, one_mul] using hh.le

theorem finiteRank_integral_two_bound {n : ℕ} (hseed : UniformCompactMatrixSeed n) :
    CompactProcessScaledIntegratedEnergyBound n 1 8 1 := by
  intro μ inst hμ hadm Ω mΩ P instP W D u
  simpa only [one_mul] using D.integratedEnergy_two_le_eight hμ hadm
    (usualFiltration_beforeZero W) (usualFiltration_null W) u (hseed μ hμ hadm Ω P W D)

theorem finiteRank_integral_three_bound {n : ℕ} (hseed : UniformCompactMatrixSeed n) :
    CompactProcessScaledIntegratedEnergyBound n 2 672 1 := by
  intro μ inst hμ hadm Ω mΩ P instP W D u
  have hC : ∀ j, 1 ≤ j → j < 2 → CompactCumulantEnergyBound n j
      (1 * finiteRankCumulantWeight j * cumulantEnergyMajorant 1 j) := by
    intro j hj hlt
    have he : j = 1 := by omega
    subst j
    norm_num [finiteRankCumulantWeight, cumulantEnergyMajorant]
    exact compactCumulantEnergyBound_one_exact
  have hI : ∀ j, 1 ≤ j → j < 2 → D.integratedEnergy (j+1) u ≤
      1 * (1 * finiteRankIntegralWeight j * cumulantEnergyMajorant 1 j) * ‖u‖^2 := by
    intro j hj hlt
    have he : j = 1 := by omega
    subst j
    norm_num [finiteRankIntegralWeight, cumulantEnergyMajorant]
    simpa only [one_mul] using finiteRank_integral_two_bound hseed μ hμ hadm Ω P W D u
  have hL := D.lowerEnergyPath_integrable_of_weighted_lower_compact_bounds hμ hadm
    (usualFiltration_beforeZero W) (usualFiltration_null W) (by norm_num : 2 ≤ 2)
    1 1 finiteRankCumulantWeight u hC
  have hl := D.integratedLowerEnergy_le_of_mixed_lower_bounds hμ hadm
    (usualFiltration_beforeZero W) (usualFiltration_null W) (by norm_num : 2 ≤ 2)
    (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) < 1)
    finiteRankCumulantWeight finiteRankCumulantWeight_nonneg finiteRankIntegralWeight 1 u hC hI
  norm_num [cumulantEnergyMajorant] at hl
  have hl0 : D.integratedLowerEnergy 2 u = 0 := le_antisymm hl (D.integratedLowerEnergy_nonnegative 2 u)
  have hh := D.expected_energy_inequality_infinite_threeSevenths_seed_eight hμ hadm
    (usualFiltration_beforeZero W) (usualFiltration_null W) (by norm_num : 2 ≤ 2) u
    (hseed μ hμ hadm Ω P W D) hL
  have he := finiteRank_integral_two_bound hseed μ hμ hadm Ω P W D u
  have hc := cumulantEnergy_nonnegative (r := 2) hμ hadm.isotropic.affineSpan_support_eq_top u 0
  rw [hl0, Real.sqrt_zero] at hh
  norm_num at hh he ⊢
  linarith

namespace MaximalProcess
variable {n : ℕ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {μ : Measure (Space n)} [IsProbabilityMeasure μ] {W : MultidimBrownianMotion P n}
  (D : MaximalProcess μ W (usualFiltration W) (usualFiltration_brownian W))

theorem finiteRank_three_process_bounds (hμ : IsCompact μ.support) (hadm : admissibleMeasure μ)
    (hseed : UniformCompactMatrixSeed n) (u : Space n) :
    cumulantEnergy μ 3 u 0 ≤ 20736 * ‖u‖^2 ∧ D.integratedEnergy 4 u ≤ 133056 * ‖u‖^2 := by
  have hC : ∀ j, 1 ≤ j → j < 3 → CompactCumulantEnergyBound n j
      (1 * finiteRankCumulantWeight j * cumulantEnergyMajorant 1 j) := by
    intro j hj hlt
    interval_cases j
    · norm_num [finiteRankCumulantWeight, cumulantEnergyMajorant]
      exact compactCumulantEnergyBound_one_exact
    · norm_num [finiteRankCumulantWeight, cumulantEnergyMajorant]
      exact compactCumulantEnergyBound_two_eight_unconditional
  have hI : ∀ j, 1 ≤ j → j < 3 → D.integratedEnergy (j+1) u ≤
      1 * (1 * finiteRankIntegralWeight j * cumulantEnergyMajorant 1 j) * ‖u‖^2 := by
    intro j hj hlt
    interval_cases j
    · norm_num [finiteRankIntegralWeight, cumulantEnergyMajorant]
      simpa only [one_mul] using finiteRank_integral_two_bound hseed μ hμ hadm Ω P W D u
    · norm_num [finiteRankIntegralWeight, cumulantEnergyMajorant]
      simpa only [one_mul] using finiteRank_integral_three_bound hseed μ hμ hadm Ω P W D u
  have hL := D.lowerEnergyPath_integrable_of_weighted_lower_compact_bounds hμ hadm
    (usualFiltration_beforeZero W) (usualFiltration_null W) (by norm_num : 2 ≤ 3)
    1 1 finiteRankCumulantWeight u hC
  have hl := D.integratedLowerEnergy_le_of_mixed_lower_bounds hμ hadm
    (usualFiltration_beforeZero W) (usualFiltration_null W) (by norm_num : 2 ≤ 3)
    (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) < 1)
    finiteRankCumulantWeight finiteRankCumulantWeight_nonneg finiteRankIntegralWeight 1 u hC hI
  norm_num [cumulantEnergyMajorant, finiteRankIntegralWeight, finiteRankCumulantWeight] at hl
  have hl' : D.integratedLowerEnergy 3 u ≤ 576 * ‖u‖^2 := by nlinarith [hl]
  have he : D.integratedEnergy 3 u ≤ 672 * ‖u‖^2 := by
    simpa only [one_mul] using finiteRank_integral_three_bound hseed μ hμ hadm Ω P W D u
  have hroot := RouteArithmetic.sqrt_product_le_of_scaled_bounds
    (D.integratedEnergy_nonnegative hμ hadm 3 u) (D.integratedLowerEnergy_nonnegative 3 u)
    (sq_nonneg ‖u‖) (by norm_num : (0 : ℝ) ≤ 672) (by norm_num : (0 : ℝ) ≤ 624)
    he hl' (by norm_num : (672 : ℝ)*576 ≤ 624^2)
  have hc := D.expected_energy_inequality_infinite_zeroCoercivity_seed_eight hμ hadm
    (usualFiltration_beforeZero W) (usualFiltration_null W) (by norm_num : 2 ≤ 3) u
    (hseed μ hμ hadm Ω P W D) hL
  have hi := D.expected_energy_inequality_infinite_threeSevenths_seed_eight hμ hadm
    (usualFiltration_beforeZero W) (usualFiltration_null W) (by norm_num : 2 ≤ 3) u
    (hseed μ hμ hadm Ω P W D) hL
  have hn := cumulantEnergy_nonnegative (r := 3) hμ hadm.isotropic.affineSpan_support_eq_top u 0
  norm_num at hc hi
  constructor <;> nlinarith

end MaximalProcess

theorem finiteRank_cumulant_three_bound {n : ℕ} (hseed : UniformCompactMatrixSeed n) :
    CompactCumulantEnergyBound n 3 20736 := by
  apply compactCumulantEnergyBound_of_weightedProcessBound (θ := 0) (by norm_num)
  intro μ inst hμ hadm Ω mΩ P instP W D u
  simpa only [zero_mul, add_zero] using (D.finiteRank_three_process_bounds hμ hadm hseed u).1

theorem finiteRank_integral_four_bound {n : ℕ} (hseed : UniformCompactMatrixSeed n) :
    CompactProcessScaledIntegratedEnergyBound n 3 133056 1 := by
  intro μ inst hμ hadm Ω mΩ P instP W D u
  simpa only [one_mul] using (D.finiteRank_three_process_bounds hμ hadm hseed u).2

theorem finiteRank_cumulant_four_bound {n : ℕ} (hseed : UniformCompactMatrixSeed n) :
    CompactCumulantEnergyBound n 4 8928000 := by
  apply compactCumulantEnergyBound_of_weightedProcessBound (θ := 0) (by norm_num)
  intro μ inst hμ hadm Ω mΩ P instP W D u
  have hC : ∀ j, 1 ≤ j → j < 4 → CompactCumulantEnergyBound n j
      (1 * finiteRankCumulantWeight j * cumulantEnergyMajorant 1 j) := by
    intro j hj hlt
    interval_cases j
    · norm_num [finiteRankCumulantWeight, cumulantEnergyMajorant]
      exact compactCumulantEnergyBound_one_exact
    · norm_num [finiteRankCumulantWeight, cumulantEnergyMajorant]
      exact compactCumulantEnergyBound_two_eight_unconditional
    · norm_num [finiteRankCumulantWeight, cumulantEnergyMajorant]
      exact finiteRank_cumulant_three_bound hseed
  have hI : ∀ j, 1 ≤ j → j < 4 → D.integratedEnergy (j+1) u ≤
      1 * (1 * finiteRankIntegralWeight j * cumulantEnergyMajorant 1 j) * ‖u‖^2 := by
    intro j hj hlt
    interval_cases j
    · norm_num [finiteRankIntegralWeight, cumulantEnergyMajorant]
      simpa only [one_mul] using finiteRank_integral_two_bound hseed μ hμ hadm Ω P W D u
    · norm_num [finiteRankIntegralWeight, cumulantEnergyMajorant]
      simpa only [one_mul] using finiteRank_integral_three_bound hseed μ hμ hadm Ω P W D u
    · norm_num [finiteRankIntegralWeight, cumulantEnergyMajorant]
      simpa only [one_mul] using finiteRank_integral_four_bound hseed μ hμ hadm Ω P W D u
  have hL := D.lowerEnergyPath_integrable_of_weighted_lower_compact_bounds hμ hadm
    (usualFiltration_beforeZero W) (usualFiltration_null W) (by norm_num : 2 ≤ 4)
    1 1 finiteRankCumulantWeight u hC
  have hl := D.integratedLowerEnergy_le_of_mixed_lower_bounds hμ hadm
    (usualFiltration_beforeZero W) (usualFiltration_null W) (by norm_num : 2 ≤ 4)
    (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) < 1)
    finiteRankCumulantWeight finiteRankCumulantWeight_nonneg finiteRankIntegralWeight 1 u hC hI
  norm_num [cumulantEnergyMajorant, finiteRankIntegralWeight, finiteRankCumulantWeight,
    Finset.sum_Icc_succ_top] at hl
  have hl' : D.integratedLowerEnergy 4 u ≤ 5695488 * ‖u‖^2 := by nlinarith [hl]
  have he : D.integratedEnergy 4 u ≤ 133056 * ‖u‖^2 := by
    simpa only [one_mul] using finiteRank_integral_four_bound hseed μ hμ hadm Ω P W D u
  have hroot := RouteArithmetic.sqrt_product_le_of_scaled_bounds
    (D.integratedEnergy_nonnegative hμ hadm 4 u) (D.integratedLowerEnergy_nonnegative 4 u)
    (sq_nonneg ‖u‖) (by norm_num : (0 : ℝ) ≤ 133056) (by norm_num : (0 : ℝ) ≤ 871488)
    he hl' (by norm_num : (133056 : ℝ)*5695488 ≤ 871488^2)
  have hc := D.expected_energy_inequality_infinite_zeroCoercivity_seed_eight hμ hadm
    (usualFiltration_beforeZero W) (usualFiltration_null W) (by norm_num : 2 ≤ 4) u
    (hseed μ hμ hadm Ω P W D) hL
  norm_num at hc ⊢
  nlinarith

end AdaptiveLocalization
end KLS
end

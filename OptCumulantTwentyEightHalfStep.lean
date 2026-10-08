import OptMixedLowerIntegral
import OptThreeSeventhsEnergyInfinite
import OptCumulantTwentyEightHalfArithmetic

/-! The actual energy step separates the compact cumulant envelope from
the integrated-energy envelope and retains the second-cumulant improvement. -/
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped NNReal ENNReal Topology BigOperators Matrix.Norms.Elementwise
noncomputable section
namespace KLS.AdaptiveLocalization
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
open LevyStochCalc.Brownian.Ito KLS.LocalDiffusion KLSLevyProbe
universe v
variable {n r : ℕ} {Ω : Type v} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {μ : Measure (Space n)} [IsProbabilityMeasure μ]
  {W : MultidimBrownianMotion P n} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ}
namespace MaximalProcess
variable (D : MaximalProcess μ W ℱ hW)
variable (hμ : IsCompact μ.support) (hadm : admissibleMeasure μ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[ℱ 0] A)

include hμ hadm hℱ0 hnull

theorem compact_energy_induction_step_twentyEightHalf (hr : 2 ≤ r) (u : Space n)
    (hseed : D.EnergyMatrixSeed)
    (hC : ∀ j, 1 ≤ j → j < r → CompactCumulantEnergyBound n j
      ((43/1000 : ℝ) * twentyEightHalfCumulantWeight j * cumulantEnergyMajorant (57/2) j))
    (hI : ∀ j, 1 ≤ j → j < r → D.integratedEnergy (j+1) u ≤
      (7/3 : ℝ) * ((43/1000 : ℝ) * twentyEightHalfIntegralWeight j * cumulantEnergyMajorant (57/2) j) * ‖u‖^2) :
    cumulantEnergy μ r u 0 + (3/7 : ℝ) * D.integratedEnergy (r+1) u ≤
      ((43/1000 : ℝ) * twentyEightHalfIntegralWeight r * cumulantEnergyMajorant (57/2) r) * ‖u‖^2 := by
  have hmajor : 0 < cumulantEnergyMajorant (57/2) (r-1) := cumulantEnergyMajorant_pos (by norm_num) _
  have hL := D.lowerEnergyPath_integrable_of_weighted_lower_compact_bounds hμ hadm hℱ0 hnull hr
    (43/1000) (57/2) twentyEightHalfCumulantWeight u hC
  have hlow := D.integratedLowerEnergy_le_of_mixed_lower_bounds hμ hadm hℱ0 hnull hr
    (by norm_num : (0 : ℝ) ≤ 43/1000) (by norm_num : (0 : ℝ) < 57/2)
    twentyEightHalfCumulantWeight (fun j => (twentyEightHalfCumulantWeight_pos j).le)
    twentyEightHalfIntegralWeight (7/3) u hC hI
  have he : D.integratedEnergy r u ≤ (7/3 : ℝ) * twentyEightHalfIntegralWeight (r-1) *
      ((43/1000 : ℝ) * cumulantEnergyMajorant (57/2) (r-1) * ‖u‖^2) := by
    have hh := hI (r-1) (by omega) (by omega)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ r)] at hh
    convert hh using 1
    ring
  have hrec : ((43/1000 : ℝ) * twentyEightHalfIntegralWeight r * cumulantEnergyMajorant (57/2) r) * ‖u‖^2 =
      (57/2 : ℝ) * (r : ℝ)^2 * twentyEightHalfIntegralWeight r *
        ((43/1000 : ℝ) * cumulantEnergyMajorant (57/2) (r-1) * ‖u‖^2) := by
    rw [cumulantEnergyMajorant_step (57/2) (by omega : 1 ≤ r)]
    ring
  have hlow' : D.integratedLowerEnergy r u ≤
      (5719/2000 : ℝ) * ((r-2 : ℕ) : ℝ) * twentyEightHalfRankConvolution r * (r : ℝ)^2 *
        ((43/1000 : ℝ) * cumulantEnergyMajorant (57/2) (r-1) * ‖u‖^2) := by
    rw [cumulantEnergyMajorant_step (57/2) (by omega : 1 ≤ r)] at hlow
    change _ ≤ _ * twentyEightHalfRankConvolution r at hlow
    convert hlow using 1
    ring
  calc
    _ ≤ (((r+2 : ℕ) : ℝ) + 2*(r : ℝ)*(5*(r : ℝ)-2)) * D.integratedEnergy r u +
        2 * Real.sqrt (D.integratedEnergy r u) * Real.sqrt (D.integratedLowerEnergy r u) :=
      D.expected_energy_inequality_infinite_threeSevenths_seed_eight hμ hadm hℱ0 hnull hr u hseed hL
    _ ≤ _ := KLS.RouteArithmetic.energy_induction_scalar_step_twentyEightHalf r hr
      (by positivity : 0 ≤ (43/1000 : ℝ) * cumulantEnergyMajorant (57/2) (r-1) * ‖u‖^2)
      (D.integratedEnergy_nonnegative hμ hadm r u) (D.integratedLowerEnergy_nonnegative r u)
      hrec he hlow'

end MaximalProcess
end KLS.AdaptiveLocalization
end

import OptWeightedLowerIntegralBeta
import OptThreeSeventhsEnergyInfinite
import OptCumulantTwentyNineArithmetic

/-! The actual energy step with a finite initial envelope and factorial
base twenty-nine, using the three-sevenths coercive coefficient. -/
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

theorem compact_energy_induction_step_twentyNine (hr : 2 ≤ r) (u : Space n)
    (hseed : D.EnergyMatrixSeed)
    (hC : ∀ j, 1 ≤ j → j < r → CompactCumulantEnergyBound n j
      ((1/20 : ℝ) * twentyNineRankWeight j * cumulantEnergyMajorant 29 j))
    (hI : ∀ j, 1 ≤ j → j < r → D.integratedEnergy (j+1) u ≤
      (7/3 : ℝ) * ((1/20 : ℝ) * twentyNineRankWeight j * cumulantEnergyMajorant 29 j) * ‖u‖^2) :
    cumulantEnergy μ r u 0 + (3/7 : ℝ) * D.integratedEnergy (r+1) u ≤
      ((1/20 : ℝ) * twentyNineRankWeight r * cumulantEnergyMajorant 29 r) * ‖u‖^2 := by
  have hmajor : 0 < cumulantEnergyMajorant 29 (r-1) := cumulantEnergyMajorant_pos (by norm_num) _
  have hL := D.lowerEnergyPath_integrable_of_weighted_lower_compact_bounds hμ hadm hℱ0 hnull hr
    (1/20) 29 twentyNineRankWeight u hC
  have hlow := D.integratedLowerEnergy_le_of_weighted_lower_bounds_beta hμ hadm hℱ0 hnull hr
    (by norm_num : (0 : ℝ) ≤ 1/20) (by norm_num : (0 : ℝ) < 29)
    twentyNineRankWeight (fun j => (twentyNineRankWeight_pos j).le) (7/3) u hC hI
  have he : D.integratedEnergy r u ≤ (7/3 : ℝ) * twentyNineRankWeight (r-1) *
      ((1/20 : ℝ) * cumulantEnergyMajorant 29 (r-1) * ‖u‖^2) := by
    have hh := hI (r-1) (by omega) (by omega)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ r)] at hh
    convert hh using 1
    ring
  have hrec : ((1/20 : ℝ) * twentyNineRankWeight r * cumulantEnergyMajorant 29 r) * ‖u‖^2 =
      29 * (r : ℝ)^2 * twentyNineRankWeight r *
        ((1/20 : ℝ) * cumulantEnergyMajorant 29 (r-1) * ‖u‖^2) := by
    rw [cumulantEnergyMajorant_step 29 (by omega : 1 ≤ r)]
    ring
  have hlow' : D.integratedLowerEnergy r u ≤
      (203/60 : ℝ) * ((r-2 : ℕ) : ℝ) * twentyNineRankConvolution r * (r : ℝ)^2 *
        ((1/20 : ℝ) * cumulantEnergyMajorant 29 (r-1) * ‖u‖^2) := by
    rw [cumulantEnergyMajorant_step 29 (by omega : 1 ≤ r)] at hlow
    change _ ≤ _ * twentyNineRankConvolution r at hlow
    convert hlow using 1
    ring
  calc
    _ ≤ (((r+2 : ℕ) : ℝ) + 2*(r : ℝ)*(5*(r : ℝ)-2)) * D.integratedEnergy r u +
        2 * Real.sqrt (D.integratedEnergy r u) * Real.sqrt (D.integratedLowerEnergy r u) :=
      D.expected_energy_inequality_infinite_threeSevenths_seed_eight hμ hadm hℱ0 hnull hr u hseed hL
    _ ≤ _ := KLS.RouteArithmetic.energy_induction_scalar_step_twentyNine r hr
      (by positivity : 0 ≤ (1/20 : ℝ) * cumulantEnergyMajorant 29 (r-1) * ‖u‖^2)
      (D.integratedEnergy_nonnegative hμ hadm r u) (D.integratedLowerEnergy_nonnegative r u)
      hrec he hlow'

end MaximalProcess
end KLS.AdaptiveLocalization
end

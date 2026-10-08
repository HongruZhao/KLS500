import OptTwentySevenBase

/-! Separate zero-coercivity compact and positive-coercivity integrated
energy estimates close the all-degree 27 induction. -/
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

theorem twentySeven_energy_induction_step (hr : 17 ≤ r) (u : Space n)
    (hseed : D.EnergyMatrixSeed)
    (hC : ∀ j, 1 ≤ j → j < r → CompactCumulantEnergyBound n j
      ((43/2000 : ℝ)*twentySevenCumulantWeight j*cumulantEnergyMajorant (27) j))
    (hI : ∀ j, 1 ≤ j → j < r → D.integratedEnergy (j+1) u ≤
      ((13/125 : ℝ)*twentySevenIntegralWeight j*cumulantEnergyMajorant (27) j)*‖u‖^2) :
    (cumulantEnergy μ r u 0 ≤
      ((43/2000 : ℝ)*twentySevenCumulantWeight r*cumulantEnergyMajorant (27) r)*‖u‖^2) ∧
    D.integratedEnergy (r+1) u ≤
      ((13/125 : ℝ)*twentySevenIntegralWeight r*cumulantEnergyMajorant (27) r)*‖u‖^2 := by
  let Q := cumulantEnergyMajorant (27) (r-1)*‖u‖^2
  have hQ : 0 ≤ Q := mul_nonneg (cumulantEnergyMajorant_pos (by norm_num) (r-1)).le (sq_nonneg ‖u‖)
  have hC' : ∀ j, 1 ≤ j → j < r → CompactCumulantEnergyBound n j
      (1*((43/2000 : ℝ)*twentySevenCumulantWeight j)*cumulantEnergyMajorant (27) j) := by
    simpa only [one_mul] using hC
  have hI' : ∀ j, 1 ≤ j → j < r → D.integratedEnergy (j+1) u ≤
      1*(1*((13/125 : ℝ)*twentySevenIntegralWeight j)*cumulantEnergyMajorant (27) j)*‖u‖^2 := by
    simpa only [one_mul] using hI
  have hL := D.lowerEnergyPath_integrable_of_weighted_lower_compact_bounds hμ hadm hℱ0 hnull (by omega : 2 ≤ r)
    1 (27) (fun j => (43/2000 : ℝ)*twentySevenCumulantWeight j) u hC'
  have hlow := D.integratedLowerEnergy_le_of_mixed_lower_bounds hμ hadm hℱ0 hnull (by omega : 2 ≤ r)
    (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) < 27)
    (fun j => (43/2000 : ℝ)*twentySevenCumulantWeight j)
    (fun j => mul_nonneg (by norm_num) (twentySevenCumulantWeight_pos j).le)
    (fun j => (13/125 : ℝ)*twentySevenIntegralWeight j) 1 u hC' hI'
  have he : D.integratedEnergy r u ≤ (13/125 : ℝ)*Q := by
    have hh := hI (r-1) (by omega) (by omega)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ r), twentySevenIntegralWeight_large (by omega : 16 ≤ r-1)] at hh
    simpa only [Q, mul_one, mul_assoc] using hh
  have hconv : (∑ j ∈ Finset.Icc 1 (r-2),
      ((13/125 : ℝ)*twentySevenIntegralWeight j)*
        ((43/2000 : ℝ)*twentySevenCumulantWeight (r-j))) =
      (43/2000 : ℝ)*(13/125)*twentySevenRankConvolution r := by
    simp only [twentySevenRankConvolution, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hconv] at hlow
  have hl : D.integratedLowerEnergy r u ≤
      (((r-2 : ℕ) : ℝ)*((43/2000 : ℝ)*(13/125)*twentySevenRankConvolution r)*(27)*(r : ℝ)^2)*Q := by
    rw [cumulantEnergyMajorant_step (27) (by omega : 1 ≤ r)] at hlow
    convert hlow using 1
    dsimp [Q]
    ring
  have hroot := RouteArithmetic.sqrt_product_le_of_scaled_bounds
    (D.integratedEnergy_nonnegative hμ hadm r u) (D.integratedLowerEnergy_nonnegative r u)
    hQ (by norm_num : (0 : ℝ) ≤ 13/125)
    (show 0 ≤ (159/2000 : ℝ)*((r : ℝ)+2)*(r : ℝ) by positivity)
    he hl (RouteArithmetic.twentySeven_root_allowance_square hr)
  have hr' : (17 : ℝ) ≤ r := by exact_mod_cast hr
  have hfactorI : 0 ≤ 5*(r : ℝ)-2 := by linarith
  have hfactorC : 0 ≤ (r : ℝ)-1 := by linarith
  have hrec (a : ℝ) : (a*cumulantEnergyMajorant (27) r)*‖u‖^2 =
      a*(27)*(r : ℝ)^2*Q := by
    dsimp [Q]
    rw [cumulantEnergyMajorant_step (27) (by omega : 1 ≤ r)]
    ring
  rw [twentySevenCumulantWeight_large (by omega : 16 ≤ r),
    twentySevenIntegralWeight_large (by omega : 16 ≤ r)]
  simp only [mul_one]
  constructor
  · have hc := D.expected_energy_inequality_infinite_zeroCoercivity_seed_eight hμ hadm hℱ0 hnull (by omega : 2 ≤ r) u hseed hL
    have hmain := mul_le_mul_of_nonneg_left he
      (show 0 ≤ (((r+2 : ℕ) : ℝ)+4*(r : ℝ)*((r : ℝ)-1)) by positivity)
    have hcoef := mul_le_mul_of_nonneg_right (RouteArithmetic.twentySeven_cumulant_coefficient hr) hQ
    rw [hrec]
    nlinarith
  · have hi := D.expected_energy_inequality_infinite_threeSevenths_seed_eight hμ hadm hℱ0 hnull (by omega : 2 ≤ r) u hseed hL
    have hmain := mul_le_mul_of_nonneg_left he
      (show 0 ≤ (((r+2 : ℕ) : ℝ)+2*(r : ℝ)*(5*(r : ℝ)-2)) by positivity)
    have hcoef := mul_le_mul_of_nonneg_right (RouteArithmetic.twentySeven_integral_coefficient hr) hQ
    have hn := cumulantEnergy_nonnegative (r := r) hμ hadm.isotropic.affineSpan_support_eq_top u 0
    rw [hrec]
    nlinarith

end MaximalProcess
end KLS.AdaptiveLocalization
end

import OptEighteenFifthBase

set_option maxRecDepth 8192

/-! Separate zero-coercivity compact and positive-coercivity integrated
energy estimates close the all-degree 91/5 induction. -/
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

theorem eighteenFifth_energy_induction_step (hr : 129 ≤ r) (u : Space n)
    (hseed : D.EnergyMatrixSeed) (hcubic : D.EnergyCubicSeed)
    (hC : ∀ j, 1 ≤ j → j < r → CompactCumulantEnergyBound n j
      ((63/500 : ℝ)*eighteenFifthCumulantWeight j*cumulantEnergyMajorant (91/5) j))
    (hI : ∀ j, 1 ≤ j → j < r → D.integratedEnergy (j+1) u ≤
      ((9/20 : ℝ)*eighteenFifthIntegralWeight j*cumulantEnergyMajorant (91/5) j)*‖u‖^2) :
    (cumulantEnergy μ r u 0 ≤
      ((63/500 : ℝ)*eighteenFifthCumulantWeight r*cumulantEnergyMajorant (91/5) r)*‖u‖^2) ∧
    D.integratedEnergy (r+1) u ≤
      ((9/20 : ℝ)*eighteenFifthIntegralWeight r*cumulantEnergyMajorant (91/5) r)*‖u‖^2 := by
  let Q := cumulantEnergyMajorant (91/5) (r-1)*‖u‖^2
  have hQ : 0 ≤ Q := mul_nonneg (cumulantEnergyMajorant_pos (by norm_num) (r-1)).le (sq_nonneg ‖u‖)
  have hC' : ∀ j, 1 ≤ j → j < r → CompactCumulantEnergyBound n j
      (1*((63/500 : ℝ)*eighteenFifthCumulantWeight j)*cumulantEnergyMajorant (91/5) j) := by
    simpa only [one_mul] using hC
  have hI' : ∀ j, 1 ≤ j → j < r → D.integratedEnergy (j+1) u ≤
      1*(1*((9/20 : ℝ)*eighteenFifthIntegralWeight j)*cumulantEnergyMajorant (91/5) j)*‖u‖^2 := by
    simpa only [one_mul] using hI
  have hL := D.lowerEnergyPath_integrable_of_weighted_lower_compact_bounds hμ hadm hℱ0 hnull (by omega : 2 ≤ r)
    1 (91/5) (fun j => (63/500 : ℝ)*eighteenFifthCumulantWeight j) u hC'
  have hlow := D.integratedLowerEnergy_le_of_mixed_lower_bounds hμ hadm hℱ0 hnull (by omega : 2 ≤ r)
    (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) < 91/5)
    (fun j => (63/500 : ℝ)*eighteenFifthCumulantWeight j)
    (fun j => mul_nonneg (by norm_num) (eighteenFifthCumulantWeight_pos j).le)
    (fun j => (9/20 : ℝ)*eighteenFifthIntegralWeight j) 1 u hC' hI'
  have he : D.integratedEnergy r u ≤ (9/20 : ℝ)*Q := by
    have hh := hI (r-1) (by omega) (by omega)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ r), eighteenFifthIntegralWeight_large (by omega : 128 ≤ r-1)] at hh
    simpa only [Q, mul_one, mul_assoc] using hh
  have hconv : (∑ j ∈ Finset.Icc 1 (r-2),
      ((9/20 : ℝ)*eighteenFifthIntegralWeight j)*
        ((63/500 : ℝ)*eighteenFifthCumulantWeight (r-j))) =
      (63/500 : ℝ)*(9/20)*eighteenFifthRankConvolution r := by
    simp only [eighteenFifthRankConvolution, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hconv] at hlow
  have hl : D.integratedLowerEnergy r u ≤
      (((r-2 : ℕ) : ℝ)*((63/500 : ℝ)*(9/20)*eighteenFifthRankConvolution r)*(91/5)*(r : ℝ)^2)*Q := by
    rw [cumulantEnergyMajorant_step (91/5) (by omega : 1 ≤ r)] at hlow
    convert hlow using 1
    dsimp [Q]
    ring
  have hroot := RouteArithmetic.sqrt_product_le_of_scaled_bounds
    (D.integratedEnergy_nonnegative hμ hadm r u) (D.integratedLowerEnergy_nonnegative r u)
    hQ (by norm_num : (0 : ℝ) ≤ 9/20)
    (show 0 ≤ (13629/20000 : ℝ)*(r : ℝ)*(r : ℝ) by positivity)
    he hl (RouteArithmetic.eighteenFifth_root_allowance_square hr)
  have hr' : (129 : ℝ) ≤ r := by exact_mod_cast hr
  have hfactorI : 0 ≤ ((4*(211/100 : ℝ)-2)*(r : ℝ)^2+(8*(211/100 : ℝ)-5)*r-2) := by nlinarith [sq_nonneg (r : ℝ)]
  have hfactorC : 0 ≤ 2*(r : ℝ)^2+3*r-2 := by nlinarith [sq_nonneg (r : ℝ)]
  have hrec (a : ℝ) : (a*cumulantEnergyMajorant (91/5) r)*‖u‖^2 =
      a*(91/5)*(r : ℝ)^2*Q := by
    dsimp [Q]
    rw [cumulantEnergyMajorant_step (91/5) (by omega : 1 ≤ r)]
    ring
  rw [eighteenFifthCumulantWeight_large (by omega : 128 ≤ r),
    eighteenFifthIntegralWeight_large (by omega : 128 ≤ r)]
  simp only [mul_one]
  constructor
  · have hc := D.expected_energy_inequality_infinite_symmetric_young hμ hadm hℱ0 hnull 1 (by norm_num) (by omega : 2 ≤ r) u hseed hcubic hL
    norm_num only [inv_one, sub_self, zero_mul, add_zero] at hc
    have hmain := mul_le_mul_of_nonneg_left he
      hfactorC
    have hcoef := mul_le_mul_of_nonneg_right (RouteArithmetic.eighteenFifth_cumulant_coefficient hr) hQ
    rw [hrec]
    nlinarith
  · have hi := D.expected_energy_inequality_infinite_symmetric_young hμ hadm hℱ0 hnull (211/100) (by norm_num) (by omega : 2 ≤ r) u hseed hcubic hL
    have hmain := mul_le_mul_of_nonneg_left he
      hfactorI
    have hcoef := mul_le_mul_of_nonneg_right (RouteArithmetic.eighteenFifth_integral_coefficient hr) hQ
    have hn := cumulantEnergy_nonnegative (r := r) hμ hadm.isotropic.affineSpan_support_eq_top u 0
    rw [hrec]
    nlinarith

end MaximalProcess
end KLS.AdaptiveLocalization
end

import OptRankYoungCertificates
import OptYoungParameterEnergyInfinite
import OptRankCauchyProcess
import OptFiniteRankFour

/-! The finite-rank scalar certificates are applied to the actual
localization energies and the proved mixed lower contraction. -/
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

theorem rankYoung_energy_induction_step (hr : 2 ≤ r) (hr16 : r ≤ 16) (u : Space n)
    (hseed : D.EnergyMatrixSeed)
    (hC : ∀ j, 1 ≤ j → j < r → CompactCumulantEnergyBound n j
      (rankYoungCumulantWeight j * cumulantEnergyMajorant 1 j))
    (hI : ∀ j, 1 ≤ j → j < r → D.integratedEnergy (j+1) u ≤
      (rankYoungIntegralWeight j * cumulantEnergyMajorant 1 j) * ‖u‖^2) :
    (3 ≤ r → cumulantEnergy μ r u 0 ≤
      (rankYoungCumulantWeight r * cumulantEnergyMajorant 1 r) * ‖u‖^2) ∧
    D.integratedEnergy (r+1) u ≤
      (rankYoungIntegralWeight r * cumulantEnergyMajorant 1 r) * ‖u‖^2 := by
  let Q := cumulantEnergyMajorant 1 (r-1) * ‖u‖^2
  have hQ : 0 ≤ Q := mul_nonneg (cumulantEnergyMajorant_pos (by norm_num) (r-1)).le (sq_nonneg ‖u‖)
  have hC' : ∀ j, 1 ≤ j → j < r → CompactCumulantEnergyBound n j
      (1 * rankYoungCumulantWeight j * cumulantEnergyMajorant 1 j) := by
    simpa only [one_mul] using hC
  have hI' : ∀ j, 1 ≤ j → j < r → D.integratedEnergy (j+1) u ≤
      1 * (1 * rankYoungIntegralWeight j * cumulantEnergyMajorant 1 j) * ‖u‖^2 := by
    simpa only [one_mul] using hI
  have hL := D.lowerEnergyPath_integrable_of_weighted_lower_compact_bounds hμ hadm hℱ0 hnull hr
    1 1 rankYoungCumulantWeight u hC'
  have hlow := D.integratedLowerEnergy_le_of_rankWeighted_lower_bounds hμ hadm hℱ0 hnull hr
    (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) < 1)
    rankYoungCumulantWeight rankYoungCumulantWeight_nonneg rankYoungIntegralWeight 1 (rankYoungCauchyWeight r) (rankYoungCauchyWeight_pos r) u hC' hI'
  have he : D.integratedEnergy r u ≤ rankYoungIntegralWeight (r-1) * Q := by
    have hh := hI (r-1) (by omega) (by omega)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ r)] at hh
    simpa only [Q, mul_assoc] using hh
  have hl : D.integratedLowerEnergy r u ≤
      (rankYoungConvolution r * (r : ℝ)^2) * Q := by
    rw [cumulantEnergyMajorant_step 1 (by omega : 1 ≤ r)] at hlow
    convert hlow using 1
    dsimp [Q, rankYoungConvolution]
    ring
  have hAB : rankYoungIntegralWeight (r-1) *
      (rankYoungConvolution r * (r : ℝ)^2) ≤
        (rankYoungRootAllowance r * (r : ℝ))^2 := by
    have hh := mul_le_mul_of_nonneg_right
      (RouteArithmetic.rankYoung_root_allowance_square r hr hr16) (sq_nonneg (r : ℝ))
    convert hh using 1 <;> ring
  have hroot := RouteArithmetic.sqrt_product_le_of_scaled_bounds
    (D.integratedEnergy_nonnegative hμ hadm r u) (D.integratedLowerEnergy_nonnegative r u)
    hQ (rankYoungIntegralWeight_nonneg _) (mul_nonneg (rankYoungRootAllowance_nonneg r) (Nat.cast_nonneg r))
    he hl hAB
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hη : 1 ≤ rankYoungParameter r := (rankYoungParameter_one_lt r).le
  have hfactorI : 0 ≤ (2*rankYoungParameter r-1)*(r : ℝ)-1 := by
    nlinarith [mul_nonneg (show 0 ≤ rankYoungParameter r-1 by linarith) (Nat.cast_nonneg (α := ℝ) r)]
  have hfactorC : 0 ≤ (r : ℝ)-1 := by linarith
  have hrec (q : ℝ) : (q * cumulantEnergyMajorant 1 r) * ‖u‖^2 =
      (r : ℝ)^2 * q * Q := by
    dsimp [Q]
    rw [cumulantEnergyMajorant_step 1 (by omega : 1 ≤ r)]
    ring
  constructor
  · intro hr3
    have hc := D.expected_energy_inequality_infinite_zeroCoercivity_seed_eight hμ hadm hℱ0 hnull hr u hseed hL
    have hmain := mul_le_mul_of_nonneg_left he
      (show 0 ≤ (((r+2 : ℕ) : ℝ) + 4*(r : ℝ)*((r : ℝ)-1)) by positivity)
    have hcoef := mul_le_mul_of_nonneg_right
      (RouteArithmetic.rankYoung_cumulant_coefficient r hr3 hr16) hQ
    rw [hrec]
    nlinarith
  · have hi := D.expected_energy_inequality_infinite_youngParameter_seed_eight hμ hadm hℱ0 hnull (rankYoungParameter r) hη hr u hseed hL
    have hmain := mul_le_mul_of_nonneg_left he
      (show 0 ≤ (((r+2 : ℕ) : ℝ) + 4*(r : ℝ)*((2*rankYoungParameter r-1)*(r : ℝ)-1)) by positivity)
    have hcoef := mul_le_mul_of_nonneg_right
      (RouteArithmetic.rankYoung_integral_coefficient r hr hr16) hQ
    have hn := cumulantEnergy_nonnegative (r := r) hμ hadm.isotropic.affineSpan_support_eq_top u 0
    apply le_of_mul_le_mul_left ?_ (rankYoungCoercivity_pos r)
    rw [hrec]
    change _ + rankYoungCoercivity r * _ ≤ _ at hi
    nlinarith

end MaximalProcess
end KLS.AdaptiveLocalization
end

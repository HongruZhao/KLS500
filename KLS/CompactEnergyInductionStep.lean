import KLS.AdaptiveLowerEnergyIntegral
import KLS.EnergyInductionArithmetic

/-! The genuine adaptive energy step, with all lower-tensor integrability
proved and the verified C=17, K=144 arithmetic applied. The actual matrix
seed and smaller-order induction hypotheses remain explicit. -/
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

theorem compact_energy_induction_step (hr : 2 ≤ r) (u : Space n)
    (hseed : D.EnergyMatrixSeed)
    (hC : ∀ j, 1 ≤ j → j < r → CompactCumulantEnergyBound n j (cumulantEnergyMajorant 144 j))
    (hI : ∀ j, 1 ≤ j → j < r →
      D.integratedEnergy (j+1) u ≤ 2 * cumulantEnergyMajorant 144 j * ‖u‖^2) :
    cumulantEnergy μ r u 0 + (1/2 : ℝ) * D.integratedEnergy (r+1) u ≤
      cumulantEnergyMajorant 144 r * ‖u‖^2 := by
  have hL := D.lowerEnergyPath_integrable_of_lower_compact_bounds hμ hadm hℱ0 hnull hr 144 u hC
  have hlow := D.integratedLowerEnergy_le_of_lower_bounds hμ hadm hℱ0 hnull hr
    (by norm_num : (0 : ℝ) < 144) u hC hI
  have he : D.integratedEnergy r u ≤
      2 * (cumulantEnergyMajorant 144 (r-1) * ‖u‖^2) := by
    have hh := hI (r-1) (by omega) (by omega)
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ r), mul_assoc] using hh
  have hrec : cumulantEnergyMajorant 144 r * ‖u‖^2 =
      144 * (r : ℝ)^2 * (cumulantEnergyMajorant 144 (r-1) * ‖u‖^2) := by
    rw [cumulantEnergyMajorant_step 144 (by omega : 1 ≤ r)]
    ring
  have hlow' : D.integratedLowerEnergy r u ≤
      2 * ((r : ℝ)-2)^2 * (cumulantEnergyMajorant 144 r * ‖u‖^2) := by
    simpa only [Nat.cast_sub hr, Nat.cast_ofNat, mul_assoc] using hlow
  calc
    _ ≤ 17 * ((r+1 : ℕ) : ℝ)^2 * D.integratedEnergy r u +
        2 * Real.sqrt (D.integratedEnergy r u) * Real.sqrt (D.integratedLowerEnergy r u) :=
      D.expected_energy_inequality_infinite hμ hadm hℱ0 hnull hr u hseed hL
    _ ≤ _ := KLS.RouteArithmetic.energy_induction_scalar_step r hr
      (mul_nonneg (cumulantEnergyMajorant_pos (by norm_num : (0 : ℝ) < 144) _).le (sq_nonneg _))
      (D.integratedEnergy_nonnegative hμ hadm r u) (D.integratedLowerEnergy_nonnegative r u)
      hrec he hlow'

end MaximalProcess
end KLS.AdaptiveLocalization
end

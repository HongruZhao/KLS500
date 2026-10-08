import KLS.IntegratedEnergyInfinite
import OptSymmetricEnergyFinite

/-! Infinite-time expected energy estimate (92), for the actual localization
process and actual cumulant tensors. No terminal-energy limit is assumed. -/
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped NNReal ENNReal Topology BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
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

variable (η : ℝ) (hη : 1 ≤ η)
include hμ hadm hℱ0 hnull η hη

/-- The actual infinite-time estimate retains the exact quadratic drift coefficient. -/
theorem expected_energy_inequality_infinite_symmetric_young (hr : 2 ≤ r) (u : Space n)
    (hseed : D.EnergyMatrixSeed) (hcubic : D.EnergyCubicSeed)
    (hL : Integrable (Function.uncurry fun ω t => D.lowerEnergyPath r u t ω)
      (P.prod (volume.restrict (Ici (0 : ℝ))))) :
    cumulantEnergy μ r u 0 + (1-η⁻¹) * D.integratedEnergy (r+1) u ≤
      ((4*η-2)*(r : ℝ)^2+(8*η-5)*r-2) * D.integratedEnergy r u +
      2 * Real.sqrt (D.integratedEnergy r u) * Real.sqrt (D.integratedLowerEnergy r u) := by
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hfactor : 0 ≤ ((4*η-2)*(r : ℝ)^2+(8*η-5)*r-2) := by
    nlinarith [mul_nonneg (show 0 ≤ η-1 by linarith) (sq_nonneg (r : ℝ)),
      mul_nonneg (show 0 ≤ η-1 by linarith) (Nat.cast_nonneg (α := ℝ) r)]
  have hfinite : ∀ᶠ T : ℝ in atTop,
      cumulantEnergy μ r u 0 +
        (1-η⁻¹) * (∫ t in Icc (0 : ℝ) T, D.energyExpectation (r+1) u t ∂volume) ≤
        D.energyExpectation r u T +
        ((4*η-2)*(r : ℝ)^2+(8*η-5)*r-2) * D.integratedEnergy r u +
        2 * Real.sqrt (D.integratedEnergy r u) * Real.sqrt (D.integratedLowerEnergy r u) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    have h := D.expected_energy_inequality_finite_symmetric_young hμ hadm hℱ0 hnull η hη hr u hseed hcubic hL hT
    have hE := mul_le_mul_of_nonneg_left
      (D.integral_energyExpectation_Icc_le hμ hadm hℱ0 hnull (show 1 ≤ r by omega) u T)
      hfactor
    have hC := D.integral_energyCross_Icc_le hμ hadm hℱ0 hnull hr u hL T
    nlinarith
  have hleft := ((D.tendsto_integral_energyExpectation_Icc hμ hadm hℱ0 hnull
    (show 1 ≤ r+1 by omega) u).const_mul (1-η⁻¹)).const_add (cumulantEnergy μ r u 0)
  have hright := ((D.tendsto_energyExpectation_zero hμ hadm hℱ0 hnull
    (show 1 ≤ r by omega) u).add_const
      (((4*η-2)*(r : ℝ)^2+(8*η-5)*r-2) * D.integratedEnergy r u)).add_const
      (2 * Real.sqrt (D.integratedEnergy r u) * Real.sqrt (D.integratedLowerEnergy r u))
  simpa only [zero_add] using le_of_tendsto_of_tendsto hleft hright hfinite


end MaximalProcess
end KLS.AdaptiveLocalization
end

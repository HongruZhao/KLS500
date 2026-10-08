import KLS.IntegratedEnergyInfinite
import OptZeroCoercivityEnergyFinite

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

include hμ hadm hℱ0 hnull

/-- The actual infinite-time estimate retains the exact quadratic drift coefficient. -/
theorem expected_energy_inequality_infinite_zeroCoercivity_seed_eight (hr : 2 ≤ r) (u : Space n)
    (hseed : D.EnergyMatrixSeed)
    (hL : Integrable (Function.uncurry fun ω t => D.lowerEnergyPath r u t ω)
      (P.prod (volume.restrict (Ici (0 : ℝ))))) :
    cumulantEnergy μ r u 0 + (0 : ℝ) * D.integratedEnergy (r+1) u ≤
      (((r+2 : ℕ) : ℝ) + 4*(r : ℝ)*((r : ℝ)-1)) * D.integratedEnergy r u +
      2 * Real.sqrt (D.integratedEnergy r u) * Real.sqrt (D.integratedLowerEnergy r u) := by
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hfactor : 0 ≤ (r : ℝ)-1 := by linarith
  have hfinite : ∀ᶠ T : ℝ in atTop,
      cumulantEnergy μ r u 0 +
        (0 : ℝ) * (∫ t in Icc (0 : ℝ) T, D.energyExpectation (r+1) u t ∂volume) ≤
        D.energyExpectation r u T +
        (((r+2 : ℕ) : ℝ) + 4*(r : ℝ)*((r : ℝ)-1)) * D.integratedEnergy r u +
        2 * Real.sqrt (D.integratedEnergy r u) * Real.sqrt (D.integratedLowerEnergy r u) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    have h := D.expected_energy_inequality_finite_zeroCoercivity_seed_eight hμ hadm hℱ0 hnull hr u hseed hL hT
    have hE := mul_le_mul_of_nonneg_left
      (D.integral_energyExpectation_Icc_le hμ hadm hℱ0 hnull (show 1 ≤ r by omega) u T)
      (show 0 ≤ (((r+2 : ℕ) : ℝ) + 4*(r : ℝ)*((r : ℝ)-1)) by positivity)
    have hC := D.integral_energyCross_Icc_le hμ hadm hℱ0 hnull hr u hL T
    nlinarith
  have hleft := ((D.tendsto_integral_energyExpectation_Icc hμ hadm hℱ0 hnull
    (show 1 ≤ r+1 by omega) u).const_mul (0 : ℝ)).const_add (cumulantEnergy μ r u 0)
  have hright := ((D.tendsto_energyExpectation_zero hμ hadm hℱ0 hnull
    (show 1 ≤ r by omega) u).add_const
      ((((r+2 : ℕ) : ℝ) + 4*(r : ℝ)*((r : ℝ)-1)) * D.integratedEnergy r u)).add_const
      (2 * Real.sqrt (D.integratedEnergy r u) * Real.sqrt (D.integratedLowerEnergy r u))
  simpa only [zero_add] using le_of_tendsto_of_tendsto hleft hright hfinite


end MaximalProcess
end KLS.AdaptiveLocalization
end

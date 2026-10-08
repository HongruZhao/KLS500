import KLS.IntegratedEnergyFinite

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

theorem tendsto_integral_energyExpectation_Icc (hr : 1 ≤ r) (u : Space n) :
    Tendsto (fun T : ℝ => ∫ t in Icc (0 : ℝ) T, D.energyExpectation r u t ∂volume)
      atTop (𝓝 (D.integratedEnergy r u)) := by
  have hU : (⋃ T : ℝ, Icc (0 : ℝ) T) = Ici (0 : ℝ) := by
    ext t
    simp only [mem_iUnion, mem_Icc, mem_Ici]
    exact ⟨fun ⟨T, ht, _⟩ => ht, fun ht => ⟨t, ht, le_rfl⟩⟩
  have hI : IntegrableOn (D.energyExpectation r u) (⋃ T : ℝ, Icc (0 : ℝ) T) := by
    rw [hU]
    exact D.integrable_energyExpectation_Ici hμ hadm hℱ0 hnull hr u
  simpa only [hU, integratedEnergy] using tendsto_setIntegral_of_monotone
    (fun T : ℝ => measurableSet_Icc) (fun a b hab => Icc_subset_Icc_right hab) hI

theorem integral_energyExpectation_Icc_le (hr : 1 ≤ r) (u : Space n) (T : ℝ) :
    (∫ t in Icc (0 : ℝ) T, D.energyExpectation r u t ∂volume) ≤ D.integratedEnergy r u :=
  setIntegral_mono_set (D.integrable_energyExpectation_Ici hμ hadm hℱ0 hnull hr u)
    (Eventually.of_forall (D.energyExpectation_nonnegative hμ hadm r u))
    (Eventually.of_forall fun _ ht => ht.1)

/-- Equation (92), with the constant 17 and the genuine lower-cumulant
integrated square. The matrix seed and finite lower energy are explicit. -/
theorem expected_energy_inequality_infinite (hr : 2 ≤ r) (u : Space n)
    (hseed : D.EnergyMatrixSeed)
    (hL : Integrable (Function.uncurry fun ω t => D.lowerEnergyPath r u t ω)
      (P.prod (volume.restrict (Ici (0 : ℝ))))) :
    cumulantEnergy μ r u 0 + (1/2 : ℝ) * D.integratedEnergy (r+1) u ≤
      17 * ((r+1 : ℕ) : ℝ)^2 * D.integratedEnergy r u +
      2 * Real.sqrt (D.integratedEnergy r u) * Real.sqrt (D.integratedLowerEnergy r u) := by
  have hfinite : ∀ᶠ T : ℝ in atTop,
      cumulantEnergy μ r u 0 +
        (1/2 : ℝ) * (∫ t in Icc (0 : ℝ) T, D.energyExpectation (r+1) u t ∂volume) ≤
        D.energyExpectation r u T +
        17 * ((r+1 : ℕ) : ℝ)^2 * D.integratedEnergy r u +
        2 * Real.sqrt (D.integratedEnergy r u) * Real.sqrt (D.integratedLowerEnergy r u) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    have h := D.expected_energy_inequality_finite hμ hadm hℱ0 hnull hr u hseed hL hT
    have hE := mul_le_mul_of_nonneg_left
      (D.integral_energyExpectation_Icc_le hμ hadm hℱ0 hnull (show 1 ≤ r by omega) u T)
      (show 0 ≤ 17 * ((r+1 : ℕ) : ℝ)^2 by positivity)
    have hC := D.integral_energyCross_Icc_le hμ hadm hℱ0 hnull hr u hL T
    nlinarith
  have hleft := ((D.tendsto_integral_energyExpectation_Icc hμ hadm hℱ0 hnull
    (show 1 ≤ r+1 by omega) u).const_mul (1/2 : ℝ)).const_add (cumulantEnergy μ r u 0)
  have hright := ((D.tendsto_energyExpectation_zero hμ hadm hℱ0 hnull
    (show 1 ≤ r by omega) u).add_const
      (17 * ((r+1 : ℕ) : ℝ)^2 * D.integratedEnergy r u)).add_const
      (2 * Real.sqrt (D.integratedEnergy r u) * Real.sqrt (D.integratedLowerEnergy r u))
  simpa only [zero_add] using le_of_tendsto_of_tendsto hleft hright hfinite

/-- The initial term is the literal squared Hilbert--Schmidt directional
cumulant slice of the original isotropic measure. -/
theorem expected_cumulant_square_inequality (hr : 2 ≤ r) (u : Space n)
    (hseed : D.EnergyMatrixSeed)
    (hL : Integrable (Function.uncurry fun ω t => D.lowerEnergyPath r u t ω)
      (P.prod (volume.restrict (Ici (0 : ℝ))))) :
    (∑ a : Fin r → Fin n, (cumulantTensor μ (r+1) (cumulantSliceDirections u a))^2) +
      (1/2 : ℝ) * D.integratedEnergy (r+1) u ≤
      17 * ((r+1 : ℕ) : ℝ)^2 * D.integratedEnergy r u +
      2 * Real.sqrt (D.integratedEnergy r u) * Real.sqrt (D.integratedLowerEnergy r u) := by
  rw [← cumulantEnergy_zero hadm.isotropic r u]
  exact D.expected_energy_inequality_infinite hμ hadm hℱ0 hnull hr u hseed hL

end MaximalProcess
end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.MaximalProcess.expected_energy_inequality_infinite
#print axioms KLS.AdaptiveLocalization.MaximalProcess.expected_cumulant_square_inequality

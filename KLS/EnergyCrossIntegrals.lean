import KLS.TensorIntegralCauchySchwarz

/-! Actual energy/cross Cauchy--Schwarz with an explicit finite lower-energy
integral. This assumption is about the genuine lower-cumulant tensor. -/
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped NNReal ENNReal Topology BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS.AdaptiveLocalization
open KLS.TensorEnergy
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
omit hℱ0 hnull in
theorem abs_energyCrossPath_le (u : Space n) (t : ℝ) (ω : Ω) :
    |D.energyCrossPath r u t ω| ≤
      Real.sqrt (D.energyPath r u t ω) * Real.sqrt (D.lowerEnergyPath r u t ω) := by
  unfold energyCrossPath energyPath lowerEnergyPath cumulantEnergyCross lowerCumulantEnergy
  rw [cumulantEnergy_eq_whitened hμ hadm.isotropic.affineSpan_support_eq_top]
  exact abs_dotProduct_le_sqrt _ _

theorem energyCrossPath_integrable_prod (hr : 2 ≤ r) (u : Space n)
    (hL : Integrable (Function.uncurry fun ω t => D.lowerEnergyPath r u t ω)
      (P.prod (volume.restrict (Ici (0 : ℝ))))) :
    Integrable (Function.uncurry fun ω t => D.energyCrossPath r u t ω)
      (P.prod (volume.restrict (Ici (0 : ℝ)))) :=
  (integrable_cross_of_energies (D.energyPath_integrable_prod hμ hadm hℱ0 hnull (by omega) u) hL
    (fun p => D.energyPath_nonnegative hμ hadm.isotropic.affineSpan_support_eq_top r u p.2 p.1)
    (fun p => D.lowerEnergyPath_nonnegative r u p.2 p.1)
    (D.energyCrossPath_measurable hμ hadm hr u).aestronglyMeasurable
    (fun p => D.abs_energyCrossPath_le hμ hadm u p.2 p.1)).1

theorem energyCrossPath_integrable_prod_Icc (hr : 2 ≤ r) (u : Space n)
    (hL : Integrable (Function.uncurry fun ω t => D.lowerEnergyPath r u t ω)
      (P.prod (volume.restrict (Ici (0 : ℝ))))) (T : ℝ) :
    Integrable (Function.uncurry fun ω t => D.energyCrossPath r u t ω)
      (P.prod (volume.restrict (Icc (0 : ℝ) T))) :=
  (D.energyCrossPath_integrable_prod hμ hadm hℱ0 hnull hr u hL).mono_measure
    (Measure.prod_mono le_rfl (Measure.restrict_mono Icc_subset_Ici_self le_rfl))

theorem integral_energyCross_Icc_le (hr : 2 ≤ r) (u : Space n)
    (hL : Integrable (Function.uncurry fun ω t => D.lowerEnergyPath r u t ω)
      (P.prod (volume.restrict (Ici (0 : ℝ))))) (T : ℝ) :
    (∫ t in Icc (0 : ℝ) T, ∫ ω, D.energyCrossPath r u t ω ∂P ∂volume) ≤
      Real.sqrt (D.integratedEnergy r u) * Real.sqrt (D.integratedLowerEnergy r u) := by
  let e : Ω × ℝ → ℝ := fun p => D.energyPath r u p.2 p.1
  let l : Ω × ℝ → ℝ := fun p => D.lowerEnergyPath r u p.2 p.1
  have he := D.energyPath_integrable_prod hμ hadm hℱ0 hnull (show 1 ≤ r by omega) u
  have he0 : ∀ p, 0 ≤ e p := fun p =>
    D.energyPath_nonnegative hμ hadm.isotropic.affineSpan_support_eq_top r u p.2 p.1
  have hl0 : ∀ p, 0 ≤ l p := fun p => D.lowerEnergyPath_nonnegative r u p.2 p.1
  obtain ⟨hs, hcs⟩ := integral_sqrt_mul_le he hL he0 hl0
  have hmeasure : P.prod (volume.restrict (Icc (0 : ℝ) T)) ≤
      P.prod (volume.restrict (Ici (0 : ℝ))) :=
    Measure.prod_mono le_rfl (Measure.restrict_mono Icc_subset_Ici_self le_rfl)
  have hcross := D.energyCrossPath_integrable_prod_Icc hμ hadm hℱ0 hnull hr u hL T
  calc
    _ = ∫ p, D.energyCrossPath r u p.2 p.1 ∂P.prod (volume.restrict (Icc (0 : ℝ) T)) :=
      (integral_prod_symm _ hcross).symm
    _ ≤ ∫ p, Real.sqrt (e p) * Real.sqrt (l p) ∂P.prod (volume.restrict (Icc (0 : ℝ) T)) :=
      integral_mono hcross (hs.mono_measure hmeasure) fun p =>
        (le_abs_self _).trans (D.abs_energyCrossPath_le hμ hadm u p.2 p.1)
    _ ≤ ∫ p, Real.sqrt (e p) * Real.sqrt (l p) ∂P.prod (volume.restrict (Ici (0 : ℝ))) :=
      integral_mono_measure hmeasure
        (Eventually.of_forall fun p => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hs
    _ ≤ _ := by
      have hEi : (∫ p, e p ∂P.prod (volume.restrict (Ici (0 : ℝ)))) =
          D.integratedEnergy r u := D.integral_prod_energyPath hμ hadm hℱ0 hnull (by omega) u
      have hLi : (∫ p, l p ∂P.prod (volume.restrict (Ici (0 : ℝ)))) =
          D.integratedLowerEnergy r u := integral_prod_symm _ hL
      change (∫ p, Real.sqrt (e p) * Real.sqrt (l p) ∂P.prod (volume.restrict (Ici (0 : ℝ)))) ≤
        Real.sqrt (∫ p, e p ∂P.prod (volume.restrict (Ici (0 : ℝ)))) *
        Real.sqrt (∫ p, l p ∂P.prod (volume.restrict (Ici (0 : ℝ)))) at hcs
      rw [hEi, hLi] at hcs
      exact hcs


end MaximalProcess
end KLS.AdaptiveLocalization
end

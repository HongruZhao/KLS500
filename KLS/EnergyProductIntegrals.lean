import KLS.EnergyLowerRegularity

/-! Genuine product-measure integrability of actual energy paths. -/
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

def lowerEnergyPath (r : ℕ) (u : Space n) (t : ℝ) (ω : Ω) : ℝ :=
  lowerCumulantEnergy μ r u (D.path t ω)

def energyCrossPath (r : ℕ) (u : Space n) (t : ℝ) (ω : Ω) : ℝ :=
  cumulantEnergyCross μ r u (D.path t ω)

def integratedEnergy (r : ℕ) (u : Space n) : ℝ :=
  ∫ t in Ici (0 : ℝ), D.energyExpectation r u t ∂volume

def integratedLowerEnergy (r : ℕ) (u : Space n) : ℝ :=
  ∫ t in Ici (0 : ℝ), ∫ ω, D.lowerEnergyPath r u t ω ∂P ∂volume

include hμ hadm hℱ0 hnull

omit hμ hadm hℱ0 hnull in
theorem lowerEnergyPath_nonnegative (r : ℕ) (u : Space n) (t : ℝ) (ω : Ω) :
    0 ≤ D.lowerEnergyPath r u t ω := lowerCumulantEnergy_nonnegative u _

omit hℱ0 hnull in
theorem lowerEnergyPath_measurable (hr : 2 ≤ r) (u : Space n) :
    Measurable (Function.uncurry fun ω t => D.lowerEnergyPath r u t ω) :=
  (continuous_lowerCumulantEnergy hμ hadm.isotropic.affineSpan_support_eq_top hr u).measurable.comp
    D.measurable_path

omit hℱ0 hnull in
theorem energyCrossPath_measurable (hr : 2 ≤ r) (u : Space n) :
    Measurable (Function.uncurry fun ω t => D.energyCrossPath r u t ω) :=
  (continuous_cumulantEnergyCross hμ hadm.isotropic.affineSpan_support_eq_top hr u).measurable.comp
    D.measurable_path

theorem integrable_energyExpectation_Ici (hr : 1 ≤ r) (u : Space n) :
    IntegrableOn (D.energyExpectation r u) (Ici (0 : ℝ)) :=
  (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr (D.integrable_energyExpectation_Ioi hμ hadm hℱ0 hnull hr u)

theorem energyPath_integrable_prod (hr : 1 ≤ r) (u : Space n) :
    Integrable (Function.uncurry fun ω t => D.energyPath r u t ω)
      (P.prod (volume.restrict (Ici (0 : ℝ)))) := by
  apply (integrable_prod_iff' (D.energyPath_measurable hμ hadm r u).aestronglyMeasurable).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    exact D.energyPath_integrable hμ hadm hℱ0 hnull hr u ht
  · have hI := D.integrable_energyExpectation_Ici hμ hadm hℱ0 hnull hr u
    change Integrable (fun t => ∫ ω, D.energyPath r u t ω ∂P) _ at hI
    convert hI using 1
    funext t
    apply integral_congr_ae
    filter_upwards [] with ω
    exact Real.norm_of_nonneg (D.energyPath_nonnegative hμ hadm.isotropic.affineSpan_support_eq_top r u t ω)

theorem energyPath_integrable_prod_Icc (hr : 1 ≤ r) (u : Space n) (T : ℝ) :
    Integrable (Function.uncurry fun ω t => D.energyPath r u t ω)
      (P.prod (volume.restrict (Icc (0 : ℝ) T))) :=
  (D.energyPath_integrable_prod hμ hadm hℱ0 hnull hr u).mono_measure
    (Measure.prod_mono le_rfl (Measure.restrict_mono Icc_subset_Ici_self le_rfl))

omit hℱ0 hnull in
theorem integratedEnergy_nonnegative (r : ℕ) (u : Space n) :
    0 ≤ D.integratedEnergy r u := integral_nonneg (D.energyExpectation_nonnegative hμ hadm r u)

omit hμ hadm hℱ0 hnull in
theorem integratedLowerEnergy_nonnegative (r : ℕ) (u : Space n) :
    0 ≤ D.integratedLowerEnergy r u :=
  integral_nonneg fun t => integral_nonneg (D.lowerEnergyPath_nonnegative r u t)

theorem integral_prod_energyPath (hr : 1 ≤ r) (u : Space n) :
    (∫ p, D.energyPath r u p.2 p.1 ∂P.prod (volume.restrict (Ici (0 : ℝ)))) =
      D.integratedEnergy r u :=
  integral_prod_symm _ (D.energyPath_integrable_prod hμ hadm hℱ0 hnull hr u)

theorem ae_continuous_integrablePath {f : (Fin (n+n*n) → ℝ) → ℝ} (hf : Continuous f)
    (T : ℝ) : ∀ᵐ ω ∂P, IntegrableOn (fun t => f (D.path t ω)) (Icc (0 : ℝ) T) := by
  filter_upwards [D.ae_continuousOn_before_lifetime, D.ae_lifetime_eq_top hμ hadm hℱ0 hnull]
    with ω hc htop
  have hsub : Icc (0 : ℝ) T ⊆ {t : ℝ | 0 ≤ t ∧ (t : WithTop ℝ) < D.lifetime ω} := by
    intro t ht
    exact ⟨ht.1, by rw [htop]; exact WithTop.coe_lt_top t⟩
  exact (hf.comp_continuousOn (hc.mono hsub)).integrableOn_compact isCompact_Icc

end MaximalProcess
end KLS.AdaptiveLocalization
end

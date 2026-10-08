import KLS.DirectionalCovarianceExpectation
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Actual energy expectations decay exponentially and are integrable at
infinity. Constants here depend on dimension and cumulant order. -/
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

def energyExpectation (r : ℕ) (u : Space n) (t : ℝ) : ℝ := ∫ ω, D.energyPath r u t ω ∂P

include hμ hadm hℱ0 hnull

omit hadm hℱ0 hnull in
theorem energyPath_nonnegative (hfull : affineSpan ℝ μ.support = ⊤)
    (r : ℕ) (u : Space n) (t : ℝ) (ω : Ω) : 0 ≤ D.energyPath r u t ω :=
  cumulantEnergy_nonnegative hμ hfull u _

omit hℱ0 hnull in
theorem energyPath_measurable (r : ℕ) (u : Space n) :
    Measurable (Function.uncurry fun ω t => D.energyPath r u t ω) :=
  (contDiff_cumulantEnergy hμ hadm.isotropic.affineSpan_support_eq_top u).continuous.measurable.comp
    D.measurable_path

omit hℱ0 hnull in
theorem energyExpectation_measurable (r : ℕ) (u : Space n) :
    Measurable (D.energyExpectation r u) :=
  (D.energyPath_measurable hμ hadm r u).stronglyMeasurable.integral_prod_left.measurable

omit hℱ0 hnull in
theorem energyExpectation_nonnegative (r : ℕ) (u : Space n) (t : ℝ) :
    0 ≤ D.energyExpectation r u t :=
  integral_nonneg fun ω => D.energyPath_nonnegative hμ hadm.isotropic.affineSpan_support_eq_top r u t ω

theorem ae_all_energyPath_le_covariance (hr : 1 ≤ r) (u : Space n) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → D.energyPath r u t ω ≤
      energyAprioriConstant n r * D.directionalCovariancePath u t ω := by
  filter_upwards [D.ae_all_localizationLaw_logConcave hμ hadm,
    D.ae_lifetime_eq_top hμ hadm hℱ0 hnull] with ω hlc htop t ht
  have ht' : (t : WithTop ℝ) < D.lifetime ω := by rw [htop]; exact WithTop.coe_lt_top t
  exact (cumulantEnergy_le_apriori_covariance hμ hadm.isotropic.affineSpan_support_eq_top
    hr u (D.path t ω) (hlc t ht ht')).trans_eq
      (congrArg (energyAprioriConstant n r * ·) (directionalCovarianceCLM_apply u _).symm)

theorem energyPath_integrable (hr : 1 ≤ r) (u : Space n) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (D.energyPath r u t) P := by
  apply ((D.directionalCovariancePath_integrable hμ u t).const_mul
    (energyAprioriConstant n r)).mono'
    (Measurable.of_uncurry_right (D.energyPath_measurable hμ hadm r u)).aestronglyMeasurable
  filter_upwards [D.ae_all_energyPath_le_covariance hμ hadm hℱ0 hnull hr u] with ω hb
  rw [Real.norm_of_nonneg (D.energyPath_nonnegative hμ hadm.isotropic.affineSpan_support_eq_top r u t ω)]
  exact hb t ht

theorem energyExpectation_le_exp_neg (hr : 1 ≤ r) (u : Space n) {t : ℝ} (ht : 0 ≤ t) :
    D.energyExpectation r u t ≤ energyAprioriConstant n r * Real.exp (-t) * ‖u‖^2 := by
  calc
    _ ≤ ∫ ω, energyAprioriConstant n r * D.directionalCovariancePath u t ω ∂P :=
      integral_mono_ae (D.energyPath_integrable hμ hadm hℱ0 hnull hr u ht)
        ((D.directionalCovariancePath_integrable hμ u t).const_mul _)
        ((D.ae_all_energyPath_le_covariance hμ hadm hℱ0 hnull hr u).mono fun _ h => h t ht)
    _ = _ := by
      rw [integral_const_mul, D.integral_directionalCovariancePath hμ hadm hℱ0 hnull u ht]
      ring

theorem integrable_energyExpectation_Ioi (hr : 1 ≤ r) (u : Space n) :
    IntegrableOn (D.energyExpectation r u) (Ioi (0 : ℝ)) := by
  apply ((integrableOn_exp_neg_Ioi 0).const_mul (energyAprioriConstant n r * ‖u‖^2)).mono'
    (D.energyExpectation_measurable hμ hadm r u).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_of_nonneg (D.energyExpectation_nonnegative hμ hadm r u t)]
  exact (D.energyExpectation_le_exp_neg hμ hadm hℱ0 hnull hr u ht.le).trans_eq (by ring)

theorem integral_energyExpectation_le_apriori (hr : 1 ≤ r) (u : Space n) :
    (∫ t in Ioi (0 : ℝ), D.energyExpectation r u t ∂volume) ≤
      energyAprioriConstant n r * ‖u‖^2 := by
  calc
    _ ≤ ∫ t in Ioi (0 : ℝ), (energyAprioriConstant n r * ‖u‖^2) * Real.exp (-t) ∂volume := by
      apply integral_mono_ae (D.integrable_energyExpectation_Ioi hμ hadm hℱ0 hnull hr u)
        ((integrableOn_exp_neg_Ioi 0).const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact (D.energyExpectation_le_exp_neg hμ hadm hℱ0 hnull hr u ht.le).trans_eq (by ring)
    _ = _ := by rw [integral_const_mul, integral_exp_neg_Ioi_zero, mul_one]

theorem tendsto_energyExpectation_zero (hr : 1 ≤ r) (u : Space n) :
    Tendsto (D.energyExpectation r u) atTop (𝓝 0) := by
  have he : Tendsto (fun t : ℝ => energyAprioriConstant n r * Real.exp (-t) * ‖u‖^2) atTop (𝓝 0) := by
    simpa using ((Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).const_mul
      (energyAprioriConstant n r)).mul_const (‖u‖^2)
  exact squeeze_zero' (Eventually.of_forall (D.energyExpectation_nonnegative hμ hadm r u))
    ((eventually_ge_atTop (0 : ℝ)).mono fun t ht =>
      D.energyExpectation_le_exp_neg hμ hadm hℱ0 hnull hr u ht) he

end MaximalProcess
end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.MaximalProcess.integrable_energyExpectation_Ioi
#print axioms KLS.AdaptiveLocalization.MaximalProcess.tendsto_energyExpectation_zero

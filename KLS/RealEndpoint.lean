import KLS.TruncationEnergy

/-!
# The literal real-integral variance formula after finiteness

Extended energy is retained until its finiteness has been proved. The real
formula below is consequently not an assertion about default values of
nonintegrable functions. It is a convention bridge, not a uniform KLS bound.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace KLS

theorem integrable_gradient_norm_sq_of_energy_lt_top
    {n : ℕ} {μ : Measure (Space n)} {f : Space n → ℝ}
    (he : energy μ f < ⊤) :
    Integrable (fun x => ‖gradient f x‖ ^ 2) μ := by
  have hm : Measurable (fun x => ENNReal.ofReal (‖gradient f x‖ ^ 2)) :=
    ((measurable_gradient f).norm.pow_const 2).ennreal_ofReal
  have hi := integrable_toReal_of_lintegral_ne_top hm.aemeasurable (ne_of_lt he)
  simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using hi

theorem energy_toReal_eq_integral_of_lt_top
    {n : ℕ} {μ : Measure (Space n)} {f : Space n → ℝ}
    (he : energy μ f < ⊤) :
    (energy μ f).toReal = ∫ x, ‖gradient f x‖ ^ 2 ∂μ := by
  exact (integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (fun x => sq_nonneg ‖gradient f x‖))
    (integrable_gradient_norm_sq_of_energy_lt_top he).aestronglyMeasurable).symm

/-- Exact variance-minus-squared-mean formulation, with every integrability
obligation explicit and proved before using the real integrals. -/
theorem finiteEnergy_real_poincare_of_mem_constants
    {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hμ : μ ≪ (volume : Measure (Space n)))
    {C : ℝ≥0} (hC : C ∈ poincareConstants μ)
    {f : Space n → ℝ} (hf : LocallyLipschitz f) (he : energy μ f < ⊤) :
    MemLp f 2 μ ∧ Integrable (fun x => ‖gradient f x‖ ^ 2) μ ∧
      ((∫ x, (f x) ^ 2 ∂μ) - (∫ x, f x ∂μ) ^ 2 ≤
        (C : ℝ) * ∫ x, ‖gradient f x‖ ^ 2 ∂μ) := by
  obtain ⟨hf2, hbound⟩ := finiteEnergy_poincare_of_mem_constants hμ hC hf he
  refine ⟨hf2, integrable_gradient_norm_sq_of_energy_lt_top he, ?_⟩
  have hright : (C : ℝ≥0∞) * energy μ f ≠ ⊤ :=
    ne_of_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top he)
  have hreal := ENNReal.toReal_mono hright hbound
  change ProbabilityTheory.variance f μ ≤ _ at hreal
  rw [ProbabilityTheory.variance_eq_sub hf2, ENNReal.toReal_mul,
    ENNReal.coe_toReal, energy_toReal_eq_integral_of_lt_top he] at hreal
  exact hreal

end KLS

#print axioms KLS.integrable_gradient_norm_sq_of_energy_lt_top
#print axioms KLS.finiteEnergy_real_poincare_of_mem_constants

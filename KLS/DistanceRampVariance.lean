import KLS.VarianceL1CutoffExtension

open MeasureTheory Set Filter Metric
open scoped Topology ContDiff ENNReal NNReal

noncomputable section
namespace KLS
variable {n : ℕ}

/-- The actual ramp gradient is integrable and its ordinary integral is bounded
by the enlargement shell divided by its width. -/
theorem distanceRamp_integral_gradient_le
    (μ : Measure (Space n)) [IsFiniteMeasure μ]
    {A : Set (Space n)} (hA : MeasurableSet A) (hne : A.Nonempty)
    {ε : ℝ} (hε : 0 < ε) :
    Integrable (gradient (distanceRamp A ε)) μ ∧
      (∫ x, ‖gradient (distanceRamp A ε) x‖ ∂μ) ≤
        ε⁻¹ * (μ (thickening ε A \ A)).toReal := by
  have hs : MeasurableSet (thickening ε A \ A) := isOpen_thickening.measurableSet.diff hA
  have hi := (integrable_const (μ := μ) (ε⁻¹ : ℝ)).indicator hs
  have hg : Integrable (gradient (distanceRamp A ε)) μ :=
    hi.mono' (measurable_gradient _).aestronglyMeasurable
      (Eventually.of_forall (distanceRamp_gradient_bound hne hε))
  refine ⟨hg,?_⟩
  have hb := integral_mono_ae hg.norm hi
    (Eventually.of_forall (distanceRamp_gradient_bound hne hε))
  simpa only [integral_indicator_const _ hs,smul_eq_mul,mul_comm,measureReal_def] using hb

/-- Retaining the full shell error gives a variance approximation for arbitrary
measurable sets, without any closure-mass assumption. -/
theorem distanceRamp_variance_shell_lower
    (μ : Measure (Space n)) [IsProbabilityMeasure μ]
    {A : Set (Space n)} (hA : MeasurableSet A) (hne : A.Nonempty)
    {ε : ℝ} (hε : 0 < ε) :
    (μ A).toReal*(1-(μ A).toReal) ≤ ProbabilityTheory.variance (distanceRamp A ε) μ +
      2*(μ (thickening ε A \ A)).toReal := by
  classical
  let r := distanceRamp A ε
  have hr0 : ∀ x, 0 ≤ r x := distanceRamp_nonneg A ε
  have hr1 : ∀ x, r x ≤ 1 := distanceRamp_le_one A hε
  have hr2 : MemLp r 2 μ := MemLp.of_bound
    (distanceRamp_lipschitz A hε).continuous.aestronglyMeasurable 1
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (hr0 x)];exact hr1 x)
  have hr := hr2.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hi := (integrable_const (μ := μ) (1 : ℝ)).indicator hA
  have hs := (integrable_const (μ := μ) (1 : ℝ)).indicator (show MeasurableSet (thickening ε A \ A) from isOpen_thickening.measurableSet.diff hA)
  have hI : (∫ x, A.indicator (fun _ => (1 : ℝ)) x ∂μ)=(μ A).toReal := by
    simp [integral_indicator_const _ hA,measureReal_def]
  have hS : (∫ x, (thickening ε A \ A).indicator (fun _ => (1 : ℝ)) x ∂μ)=
      (μ (thickening ε A \ A)).toReal  := by
    simp [integral_indicator_const _ (isOpen_thickening.measurableSet.diff hA),measureReal_def]
  have hp0 : 0 ≤ (μ A).toReal := ENNReal.toReal_nonneg
  have hp1 : (μ A).toReal ≤ 1 := by
    exact_mod_cast ENNReal.toReal_mono (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) (prob_le_one (μ := μ))
  have hm0 : 0 ≤ ∫ x, r x ∂μ := integral_nonneg hr0
  have hm1 : (∫ x, r x ∂μ) ≤ 1 := by
    simpa using integral_mono hr (integrable_const (μ := μ) (1 : ℝ)) hr1
  have hm : (∫ x, r x ∂μ) ≤ (μ A).toReal+(μ (thickening ε A \ A)).toReal := by
    rw [← hI,← hS,← integral_add hi hs]
    apply integral_mono hr (hi.add hs)
    intro x
    have he := distanceRamp_indicator_error hne hε x
    change r x ≤ A.indicator (fun _ => (1 : ℝ)) x+(thickening ε A \ A).indicator (fun _ => (1 : ℝ)) x
    change |A.indicator (fun _ => (1 : ℝ)) x-r x| ≤ _ at he
    have hl := neg_le_abs (A.indicator (fun _ => (1 : ℝ)) x-r x)
    linarith
  have hq : (μ A).toReal ≤ ∫ x, r x ^ 2 ∂μ := by
    rw [← hI]
    apply integral_mono hi hr2.integrable_sq
    intro x
    by_cases hx : x ∈ A
    · simp [hx,r,distanceRamp_eq_one hx]
    · simpa [hx] using sq_nonneg (r x)
  rw [ProbabilityTheory.variance_eq_sub hr2]
  change (μ A).toReal*(1-(μ A).toReal) ≤
    (∫ x, r x ^ 2 ∂μ)-(∫ x, r x ∂μ)^2+2*(μ (thickening ε A \ A)).toReal
  have hm2 : (∫ x, r x ∂μ)^2-(μ A).toReal^2 ≤
      2*(μ (thickening ε A \ A)).toReal := by
    have hp : (∫ x, r x ∂μ)-(μ A).toReal ≤ (μ (thickening ε A \ A)).toReal := by linarith
    by_cases hmp : (∫ x, r x ∂μ) ≤ (μ A).toReal
    · have hsq := (sq_le_sq₀ hm0 hp0).2 hmp
      nlinarith [ENNReal.toReal_nonneg (a := μ (thickening ε A \ A))]
    · have hprod := mul_le_mul_of_nonneg_left (show (∫ x, r x ∂μ)+(μ A).toReal ≤ 2 by linarith)
        (show 0 ≤ (∫ x, r x ∂μ)-(μ A).toReal by linarith)
      nlinarith
  linarith

end KLS
end

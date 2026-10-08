import KLS.NormExponentialLogLaplace

/-! The graph log-Laplace derivative in its first coordinate is the actual
normalized tilt average of the signal on the original noncompact law. -/

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology BigOperators
noncomputable section
namespace KLS

/-- Parameter paired with the literal signal graph, in the same coordinate order. -/
def suspensionGraphParameter (n : ℕ) : (ℝ × Space n) →L[ℝ] Space (n + 1) where
  toFun p := WithLp.toLp 2 (Fin.cons p.1 (fun j => p.2 j))
  map_add' p q := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  map_smul' a p := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  cont := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin (n + 1) => ℝ)).comp
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [Fin.cons_zero] using (continuous_fst : Continuous (fun p : ℝ × Space n => p.1))
    · simpa only [Fin.cons_succ] using (show Continuous (fun p : ℝ × Space n => p.2 j) by fun_prop)

lemma inner_suspensionGraphParameter {n : ℕ} (f : Space n → ℝ) (p : ℝ × Space n)
    (x : Space n) :
    inner ℝ (suspensionGraphParameter n p) (suspensionGraph f x) =
      p.1 * f x + inner ℝ p.2 x := by
  rw [inner_eq_coordinate_sum, Fin.sum_univ_succ, inner_eq_coordinate_sum]
  change f x * p.1 + (∑ i, x i * p.2 i) = p.1 * f x + (∑ i, x i * p.2 i)
  ring

lemma contDiff_graphLogLaplace_of_linear_growth {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : NormExponentialDomain μ (fun _ => 1))
    {f : Space n → ℝ} (hf : Measurable f) {A B : ℝ}
    (hbound : ∀ x, |f x| ≤ A + B * ‖x‖) :
    ContDiff ℝ (⊤ : ℕ∞) (tiltLogLaplace (μ.map (suspensionGraph f))) := by
  exact contDiff_tiltLogLaplace_of_normExponentialDomain
    (normExponentialDomain_suspensionGraph hμ hf hbound)

lemma graph_tiltPartition_at_zero_signal {n : ℕ} {μ : Measure (Space n)}
    {f : Space n → ℝ} (hf : Measurable f) (z : Space n) :
    tiltPartition (μ.map (suspensionGraph f))
      (fun y => inner ℝ (suspensionGraphParameter n (0, z)) y) =
      tiltPartition μ (fun x => inner ℝ z x) := by
  unfold tiltPartition
  rw [integral_map (measurable_suspensionGraph hf).aemeasurable (by fun_prop)]
  simp_rw [inner_suspensionGraphParameter, zero_mul, zero_add]

lemma graph_tilt_average_at_zero_signal {n : ℕ} {μ : Measure (Space n)}
    {f : Space n → ℝ} (hf : Measurable f) (z : Space n) :
    (∫ y, y 0 ∂exponentialTilt (μ.map (suspensionGraph f))
      (suspensionGraphParameter n (0, z))) = ∫ x, f x ∂exponentialTilt μ z := by
  change tiltAverage (μ.map (suspensionGraph f))
    (fun y => inner ℝ (suspensionGraphParameter n (0, z)) y) (fun y => y 0) =
      tiltAverage μ (fun x => inner ℝ z x) f
  rw [tiltAverage_eq_ratio, tiltAverage_eq_ratio]
  congr 1
  · rw [integral_map (measurable_suspensionGraph hf).aemeasurable (by fun_prop)]
    simp_rw [inner_suspensionGraphParameter, zero_mul, zero_add]
    rfl
  · exact graph_tiltPartition_at_zero_signal hf z

/-- Literal first-coordinate derivative of the graph log-Laplace transform.
Smoothness and the differentiation under the integral follow from proved
radial exponential moments, with no compact support. -/
lemma fderiv_graphLogLaplace_first_at_zero_signal {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : NormExponentialDomain μ (fun _ => 1))
    {f : Space n → ℝ} (hf : Measurable f) {A B : ℝ}
    (hbound : ∀ x, |f x| ≤ A + B * ‖x‖) (z : Space n) :
    fderiv ℝ (tiltLogLaplace (μ.map (suspensionGraph f)))
      (suspensionGraphParameter n (0, z)) (EuclideanSpace.basisFun (Fin (n + 1)) ℝ 0) =
      ∫ x, f x ∂exponentialTilt μ z := by
  rw [fderiv_tiltLogLaplace_coordinate_of_normExponentialDomain
    (normExponentialDomain_suspensionGraph hμ hf hbound)]
  exact graph_tilt_average_at_zero_signal hf z

lemma contDiff_exponentialTilt_average_of_linear_growth {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : NormExponentialDomain μ (fun _ => 1))
    {f : Space n → ℝ} (hf : Measurable f) {A B : ℝ}
    (hbound : ∀ x, |f x| ≤ A + B * ‖x‖) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => ∫ x, f x ∂exponentialTilt μ z) := by
  have he : (fun z => ∫ x, f x ∂exponentialTilt μ z) =
      (fun z => fderiv ℝ (tiltLogLaplace (μ.map (suspensionGraph f)))
        (suspensionGraphParameter n (0, z)) (EuclideanSpace.basisFun (Fin (n + 1)) ℝ 0)) := by
    funext z
    exact (fderiv_graphLogLaplace_first_at_zero_signal hμ hf hbound z).symm
  rw [he]
  exact (((contDiff_graphLogLaplace_of_linear_growth hμ hf hbound).fderiv_right (by simp)).comp
    ((suspensionGraphParameter n).contDiff.comp (contDiff_const.prodMk contDiff_id))).clm_apply
      contDiff_const

end KLS
end
#print axioms KLS.contDiff_graphLogLaplace_of_linear_growth
#print axioms KLS.fderiv_graphLogLaplace_first_at_zero_signal

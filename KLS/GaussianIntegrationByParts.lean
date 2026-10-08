import KLS.GaussianSmoothingGradient
import KLS.MomentMapSteinBound

/-!
# Gaussian integration by parts for shifted compact tests

This is an identity for the actual standard Gaussian law. It remains valid
at zero Gaussian scale. Bounds on a compact C1 test and its derivative
discharge all four integrability premises of weighted integration by parts.
-/

open MeasureTheory InnerProductSpace Set Filter
open scoped ContDiff Topology RealInnerProductSpace

noncomputable section
namespace KLS

lemma gaussianExample_eq_potentialMeasure (n : ℕ) :
    gaussianExample n = potentialMeasure (gaussianPotential n) := by
  rw [gaussianExample_eq_withDensity_prod, ← gaussianPotential_exp_density]
  rfl

lemma fderiv_gaussianPotential {n : ℕ} (x : Space n) :
    fderiv ℝ (gaussianPotential n) x = innerSL ℝ x := by
  have he : gaussianPotential n = fun z : Space n => ‖z‖ ^ 2 / 2 +
      n * Real.log (Real.sqrt (2 * Real.pi)) := funext gaussianPotential_eq_norm_sq
  have hd := (((hasStrictFDerivAt_norm_sq x).hasFDerivAt.mul_const (2 : ℝ)⁻¹).add_const
    (n * Real.log (Real.sqrt (2 * Real.pi))))
  simp only [← div_eq_mul_inv] at hd
  rw [he, hd.fderiv]
  ext y
  simp only [smul_apply, smul_eq_mul]
  ring

lemma memLp_compact_test_comp {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {f : Space n → ℝ}
    (hf : Continuous f) (hc : HasCompactSupport f) {X : Ω → Space n}
    (hX : Measurable X) : MemLp (fun x => f (X x)) 2 μ := by
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hf
  exact MemLp.of_bound (hf.measurable.comp hX).aestronglyMeasurable C
    (Eventually.of_forall fun x => hC (X x))

lemma memLp_compact_test_gradient_comp {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {f : Space n → ℝ}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) {X : Ω → Space n}
    (hX : Measurable X) : MemLp (fun x => gradient f (X x)) 2 μ := by
  obtain ⟨C, hC⟩ := (hc.fderiv ℝ).exists_bound_of_continuous
    (hf.fderiv_right (m := 0) (by norm_num)).continuous
  exact MemLp.of_bound ((measurable_gradient f).comp hX).aestronglyMeasurable C
    (Eventually.of_forall fun x => by simpa only [norm_gradient_eq_norm_fderiv] using hC (X x))

lemma integrable_inner_of_memLp_two {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {μ : Measure Ω}
    {X Y : Ω → E} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    Integrable (fun x => inner ℝ (X x) (Y x)) μ := by
  apply (hX.norm.integrable_mul hY.norm).mono'
    (hX.aestronglyMeasurable.inner hY.aestronglyMeasurable)
  exact Eventually.of_forall fun x => norm_inner_le_norm _ _

theorem integral_gaussian_shift_mul_inner {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (a w : Space n) (r : ℝ) :
    (∫ y, f (a + r • y) * inner ℝ (r • y) w ∂gaussianExample n) =
      ∫ y, inner ℝ (gradient f (a + r • y)) (r ^ 2 • w) ∂gaussianExample n := by
  let F : Space n → ℝ := fun y => f (a + r • y)
  have hF : ContDiff ℝ 1 F := hf.comp (by fun_prop)
  have hφ : Differentiable ℝ (gaussianPotential n) := by
    unfold gaussianPotential gaussianCoordinatePotential
    fun_prop
  have hF2 : MemLp F 2 (gaussianExample n) := memLp_compact_test_comp hf.continuous hc (by fun_prop)
  have hg2 := memLp_compact_test_gradient_comp (μ := gaussianExample n) hf hc
    (X := fun y => a + r • y) (by fun_prop)
  have hy2 : MemLp (fun y : Space n => inner ℝ y (r • w)) 2 (gaussianExample n) := by
    simpa only [Function.comp_def, innerSL_apply_apply, real_inner_comm] using
      (innerSL ℝ (r • w)).comp_memLp'
        (ProbabilityTheory.IsGaussian.memLp_two_fun_id (μ := gaussianExample n))
  have hd (y : Space n) : fderiv ℝ F y (r • w) =
      inner ℝ (gradient f (a + r • y)) (r ^ 2 • w) := by
    have hh := (hf.differentiable (by norm_num) (a + r • y)).hasFDerivAt.comp y
      (((hasFDerivAt_id y).const_smul r).const_add a)
    simp only [Function.comp_def, Pi.smul_apply, id_eq] at hh
    rw [show F = fun y => f (a + r • y) from rfl, hh.fderiv]
    simp only [ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply,
      smul_smul, ← pow_two, ← inner_gradient_left]
  have hd1 : Integrable (fun y => fderiv ℝ F y (r • w)) (gaussianExample n) := by
    simp_rw [hd]
    exact integrable_inner_of_memLp_two hg2 (memLp_const _)
  have hp1 : Integrable (fun y => F y * fderiv ℝ (gaussianPotential n) y (r • w))
      (gaussianExample n) := by
    simp_rw [fderiv_gaussianPotential, innerSL_apply_apply]
    exact hF2.integrable_mul hy2
  have hh := integral_mul_fderiv_potentialMeasure hφ
    (hF.differentiable (by norm_num)) (differentiable_const (1 : ℝ)) (r • w)
    (by rw [← gaussianExample_eq_potentialMeasure]; simpa using hF2.integrable (by norm_num))
    (by rw [← gaussianExample_eq_potentialMeasure]; simpa using hd1)
    (by simp)
    (by rw [← gaussianExample_eq_potentialMeasure]; simpa using hp1)
  rw [← gaussianExample_eq_potentialMeasure] at hh
  simp only [fderiv_const_apply, zero_apply, mul_zero, integral_zero, mul_one,
    fderiv_gaussianPotential, innerSL_apply_apply, hd, F, real_inner_smul_right,
    real_inner_smul_left] at hh ⊢
  linarith

end KLS
end

#print axioms KLS.integral_gaussian_shift_mul_inner

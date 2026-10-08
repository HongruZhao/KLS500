import KLS.MomentMapIntegration
import KLS.WeightedDiffusionCalculus

/-!
# Stein identity in the actual moment-map coupling

Weighted integration by parts and the chain rule identify the Stein identity
for the actual gradient pushforward. The derivative of the gradient is not an
abstract kernel. Moment-map existence is not assumed to have been proved.
-/

open MeasureTheory InnerProductSpace Set Filter
open scoped BigOperators ContDiff

noncomputable section
namespace KLS.MomentMap

variable {n : ℕ}

/-- Chain rule for a test pulled back through the genuine gradient. -/
lemma fderiv_comp_gradient_apply {φ f : Space n → ℝ}
    (hgrad : Differentiable ℝ (gradient φ)) (hf : Differentiable ℝ f)
    (x v : Space n) :
    fderiv ℝ (fun y => f (gradient φ y)) x v =
      inner ℝ (gradient f (gradient φ x)) (fderiv ℝ (gradient φ) x v) := by
  rw [fderiv_fun_comp x (hf _) (hgrad _)]
  exact inner_gradient_left.symm

/-- A coupling Stein formula with the three required integrability premises explicit. -/
theorem integral_gradient_mul_test_eq {φ f : Space n → ℝ}
    (hφ : Differentiable ℝ φ) (hgrad : Differentiable ℝ (gradient φ))
    (hf : Differentiable ℝ f) (v : Space n)
    (hfL1 : Integrable (fun x => f (gradient φ x)) (potentialMeasure φ))
    (hdL1 : Integrable (fun x =>
      inner ℝ (gradient f (gradient φ x)) (fderiv ℝ (gradient φ) x v))
      (potentialMeasure φ))
    (hpL1 : Integrable (fun x => f (gradient φ x) * fderiv ℝ φ x v)
      (potentialMeasure φ)) :
    (∫ x, f (gradient φ x) * fderiv ℝ φ x v ∂potentialMeasure φ) =
      ∫ x, inner ℝ (gradient f (gradient φ x)) (fderiv ℝ (gradient φ) x v)
        ∂potentialMeasure φ := by
  have hd : Integrable (fun x =>
      fderiv ℝ (fun y => f (gradient φ y)) x v * (1 : ℝ)) (potentialMeasure φ) := by
    simpa only [mul_one, fderiv_comp_gradient_apply hgrad hf] using hdL1
  have h := integral_mul_fderiv_potentialMeasure (f := fun x => f (gradient φ x)) hφ
    (by simpa only [Function.comp_def] using hf.comp hgrad)
    (differentiable_const (1 : ℝ)) v
    (by simpa only [mul_one] using hfL1) hd
    (by simp) (by simpa only [mul_one] using hpL1)
  simp only [fderiv_const_apply, zero_apply, mul_zero, integral_zero, mul_one,
    fderiv_comp_gradient_apply hgrad hf] at h
  linarith

/-- The left side is the actual target-law integral under the gradient pushforward. -/
theorem integral_target_mul_test_eq {φ f : Space n → ℝ}
    (hφ : Differentiable ℝ φ) (hgrad : Differentiable ℝ (gradient φ))
    (hf : Differentiable ℝ f) (v : Space n)
    (hfL1 : Integrable (fun x => f (gradient φ x)) (potentialMeasure φ))
    (hdL1 : Integrable (fun x =>
      inner ℝ (gradient f (gradient φ x)) (fderiv ℝ (gradient φ) x v))
      (potentialMeasure φ))
    (hpL1 : Integrable (fun x => f (gradient φ x) * fderiv ℝ φ x v)
      (potentialMeasure φ)) :
    (∫ z, f z * inner ℝ z v ∂gradientPushforward φ) =
      ∫ x, inner ℝ (gradient f (gradient φ x)) (fderiv ℝ (gradient φ) x v)
        ∂potentialMeasure φ := by
  unfold gradientPushforward
  rw [integral_map hgrad.continuous.measurable.aemeasurable
    (by exact (show Continuous (fun z => f z * inner ℝ z v) from
      hf.continuous.mul (continuous_id.inner continuous_const)).measurable.aestronglyMeasurable)]
  simp_rw [inner_gradient_left]
  simpa only [inner_gradient_left] using
    integral_gradient_mul_test_eq hφ hgrad hf v hfL1 hdL1 hpL1

/-- Coordinate form of the actual gradient derivative contraction. -/
lemma inner_gradient_hessian_column {φ f : Space n → ℝ}
    (hgrad : Differentiable ℝ (gradient φ)) (x : Space n) (i : Fin n) :
    inner ℝ (gradient f (gradient φ x))
      (fderiv ℝ (gradient φ) x (coordinateVector i)) =
      ∑ j : Fin n, hessianMatrix φ x j i * gradient f (gradient φ x) j := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  apply Finset.sum_congr rfl
  intro j _
  rw [hessianMatrix_apply_eq hgrad]

/-- The coupling Stein identity, with the actual coordinate Hessian. -/
theorem integral_coordinate_test_eq_hessian {φ f : Space n → ℝ}
    (hφ : Differentiable ℝ φ) (hgrad : Differentiable ℝ (gradient φ))
    (hf : Differentiable ℝ f) (i : Fin n)
    (hfL1 : Integrable (fun x => f (gradient φ x)) (potentialMeasure φ))
    (hdL1 : Integrable (fun x => ∑ j : Fin n,
      hessianMatrix φ x j i * gradient f (gradient φ x) j) (potentialMeasure φ))
    (hpL1 : Integrable (fun x => f (gradient φ x) * gradient φ x i)
      (potentialMeasure φ)) :
    (∫ z, f z * z i ∂gradientPushforward φ) =
      ∫ x, ∑ j : Fin n, hessianMatrix φ x j i * gradient f (gradient φ x) j
        ∂potentialMeasure φ := by
  have h := integral_target_mul_test_eq hφ hgrad hf (coordinateVector i) hfL1
    (by simpa only [inner_gradient_hessian_column hgrad] using hdL1)
    (by simpa only [← gradient_coordinate_eq_fderiv] using hpL1)
  simp only [inner_gradient_hessian_column hgrad] at h
  simpa only [coordinateVector, EuclideanSpace.inner_single_right,
    map_one, starRingEnd_apply, star_trivial, one_mul] using h

/-- Compact continuous tests are integrable through the actual gradient map. -/
lemma integrable_comp_gradient_of_hasCompactSupport {φ f : Space n → ℝ}
    [IsFiniteMeasure (potentialMeasure φ)]
    (hgrad : Continuous (gradient φ)) (hf : Continuous f) (hc : HasCompactSupport f) :
    Integrable (fun x => f (gradient φ x)) (potentialMeasure φ) := by
  let : IsFiniteMeasure (gradientPushforward φ) := by
    unfold gradientPushforward
    infer_instance
  have hi : Integrable f (gradientPushforward φ) :=
    hf.integrable_of_hasCompactSupport hc
  exact hi.comp_aemeasurable hgrad.measurable.aemeasurable

/-- The derivative term is integrable for compact C1 tests when the actual gradient
map is C1 with uniformly bounded derivative. No inverse-image compactness is used. -/
lemma integrable_stein_derivative_of_bound {φ f : Space n → ℝ}
    [IsFiniteMeasure (potentialMeasure φ)]
    (hgrad : ContDiff ℝ 1 (gradient φ)) (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) {M : ℝ}
    (hM : ∀ x, ‖fderiv ℝ (gradient φ) x‖ ≤ M) (v : Space n) :
    Integrable (fun x => inner ℝ (gradient f (gradient φ x))
      (fderiv ℝ (gradient φ) x v)) (potentialMeasure φ) := by
  have hgD := hgrad.differentiable (by norm_num)
  have hfD := hf.differentiable (by norm_num)
  have hFc : ContDiff ℝ 1 (fun x => f (gradient φ x)) := hf.comp hgrad
  obtain ⟨C, hC⟩ := (hc.fderiv ℝ).exists_bound_of_continuous
    (hf.fderiv_right (m := 0) (by norm_num)).continuous
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hmeas : AEStronglyMeasurable
      (fun x => fderiv ℝ (fun y => f (gradient φ y)) x v) (potentialMeasure φ) :=
    (((hFc.fderiv_right (m := 0) (by norm_num)).continuous).clm_apply
      continuous_const).aestronglyMeasurable
  have hi : Integrable (fun x => fderiv ℝ (fun y => f (gradient φ y)) x v)
      (potentialMeasure φ) := by
    apply (integrable_const (C * M * ‖v‖)).mono' hmeas
    exact Eventually.of_forall fun x => by
      rw [fderiv_fun_comp x (hfD _) (hgD _)]
      change ‖fderiv ℝ f (gradient φ x) (fderiv ℝ (gradient φ) x v)‖ ≤ _
      calc
        _ ≤ ‖fderiv ℝ f (gradient φ x)‖ * ‖fderiv ℝ (gradient φ) x v‖ :=
          ContinuousLinearMap.le_opNorm _ _
        _ ≤ C * (M * ‖v‖) := mul_le_mul (hC _) ((ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _))) (norm_nonneg _) hC0
        _ = _ := by ring
  simpa only [fderiv_comp_gradient_apply hgD hfD] using hi

/-- The actual coupling Stein identity for all compact C1 tests, with its entire
integration domain derived from finite mass and the gradient derivative bound. -/
theorem integral_target_mul_test_eq_of_hasCompactSupport {φ f : Space n → ℝ}
    [IsFiniteMeasure (potentialMeasure φ)]
    (hφ : Differentiable ℝ φ) (hgrad : ContDiff ℝ 1 (gradient φ))
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) {M : ℝ}
    (hM : ∀ x, ‖fderiv ℝ (gradient φ) x‖ ≤ M) (v : Space n) :
    (∫ z, f z * inner ℝ z v ∂gradientPushforward φ) =
      ∫ x, inner ℝ (gradient f (gradient φ x)) (fderiv ℝ (gradient φ) x v)
        ∂potentialMeasure φ := by
  apply integral_target_mul_test_eq hφ (hgrad.differentiable (by norm_num))
    (hf.differentiable (by norm_num)) v
  · exact integrable_comp_gradient_of_hasCompactSupport hgrad.continuous hf.continuous hc
  · exact integrable_stein_derivative_of_bound hgrad hf hc hM v
  · have hi := integrable_comp_gradient_of_hasCompactSupport hgrad.continuous
      (hf.continuous.mul (continuous_id.inner (continuous_const (y := v)))) hc.mul_right
    simpa only [Pi.mul_apply, id_eq, inner_gradient_left] using hi

end KLS.MomentMap
end

#print axioms KLS.MomentMap.fderiv_comp_gradient_apply
#print axioms KLS.MomentMap.integral_target_mul_test_eq
#print axioms KLS.MomentMap.integral_coordinate_test_eq_hessian

#print axioms KLS.MomentMap.integrable_stein_derivative_of_bound
#print axioms KLS.MomentMap.integral_target_mul_test_eq_of_hasCompactSupport

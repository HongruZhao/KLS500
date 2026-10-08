import KLS.WeakHessianMean
import KLS.AffineMomentMapStein
import KLS.PointwiseGradientHessian
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

open MeasureTheory ProbabilityTheory InnerProductSpace Matrix Set Filter
open scoped BigOperators ContDiff Topology NNReal ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
namespace MomentMap
variable {n : ℕ}

/-- The actual a.e. Hessian, transported by the same affine map as the law. -/
def rawTransportedHessianDerivative (φ : Space n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (x w : Space n) : Space n :=
  matrixAction A (matrixAction (coordinateHessian φ x) (matrixAction A.transpose w))

theorem memLp_matrixAction_actualHessian
    {φ : Space n → ℝ} {G : ℝ≥0} {μ : Measure (Space n)} [IsFiniteMeasure μ]
    (hG : LipschitzWith G (gradient φ)) (v : Space n) (p : ℝ≥0∞) :
    MemLp (fun x => matrixAction (coordinateHessian φ x) v) p μ := by
  apply MemLp.of_eval_piLp
  intro i
  change MemLp (fun x => ∑ j, coordinateHessian φ x i j * v j) p μ
  exact memLp_finsetSum _ fun j _ =>
    (memLp_actual_hessian_entry_of_global_gradient_lipschitz hG i j p).mul_const (v j)

theorem memLp_rawTransportedHessianDerivative
    {φ : Space n → ℝ} {G : ℝ≥0} {μ : Measure (Space n)} [IsFiniteMeasure μ]
    (hG : LipschitzWith G (gradient φ))
    (A : Matrix (Fin n) (Fin n) ℝ) (w : Space n) (p : ℝ≥0∞) :
    MemLp (fun x => rawTransportedHessianDerivative φ A x w) p μ :=
  (matrixAction A).comp_memLp'
    (memLp_matrixAction_actualHessian hG (matrixAction A.transpose w) p)

theorem memLp_comp_linear_gradient_test_raw
    {φ f : Space n → ℝ} {μ : Measure (Space n)} [IsFiniteMeasure μ]
    (hgrad : Continuous (gradient φ)) (hf : Continuous f) (hc : HasCompactSupport f)
    (A : Matrix (Fin n) (Fin n) ℝ) (p : ℝ≥0∞) :
    MemLp (fun x => f (matrixAction A (gradient φ x))) p μ := by
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hf
  exact MemLp.of_bound (hf.comp ((matrixAction A).continuous.comp hgrad)).aestronglyMeasurable
    C (Eventually.of_forall fun x => hC (matrixAction A (gradient φ x)))

/-- Actual Rademacher derivatives give the weak chain rule; no source C2 is used. -/
theorem raw_linear_gradient_test_weak_derivative
    {φ f : Space n → ℝ} {G : ℝ≥0}
    (hφ : ContDiff ℝ 1 φ) (hG : LipschitzWith G (gradient φ))
    (hf : ContDiff ℝ 1 f) (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    HasLocalWeakCoordinateDerivative (fun x => f (matrixAction A (gradient φ x)))
      (fun x => inner ℝ (gradient f (matrixAction A (gradient φ x)))
        (matrixAction A (matrixAction (coordinateHessian φ x) (EuclideanSpace.single i 1)))) i := by
  let F := fun x => f (matrixAction A (gradient φ x))
  have hF : LocallyLipschitz F := hf.locallyLipschitz.comp
    ((matrixAction A).lipschitzWith.locallyLipschitz.comp hG.locallyLipschitz)
  have he : coordinateDerivative F i =ᵐ[volume]
      (fun x => inner ℝ (gradient f (matrixAction A (gradient φ x)))
        (matrixAction A (matrixAction (coordinateHessian φ x) (EuclideanSpace.single i 1)))) := by
    filter_upwards [hG.ae_differentiableAt (μ := volume)] with x hx
    have hg := hasFDerivAt_gradient_of_differentiableAt_gradient
      (hφ.differentiable (by norm_num)) hx
    have hh := (hf.differentiable (by norm_num) (matrixAction A (gradient φ x))).hasFDerivAt.comp x
      ((matrixAction A).hasFDerivAt.comp x hg)
    have hv := congrArg (fun D : Space n →L[ℝ] ℝ => D (EuclideanSpace.single i 1)) hh.fderiv
    simpa only [F, coordinateDerivative, Function.comp_def,
      ContinuousLinearMap.comp_apply, ← inner_gradient_left] using hv
  exact (hasLocalWeakCoordinateDerivative_of_locallyLipschitz hF i).congr_ae
    Filter.EventuallyEq.rfl he

theorem inner_rawTransportedHessianDerivative_eq_sum
    (φ : Space n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (x w z : Space n) :
    inner ℝ z (rawTransportedHessianDerivative φ A x w) =
      ∑ i, (matrixAction A.transpose w) i * inner ℝ z
        (matrixAction A (matrixAction (coordinateHessian φ x) (EuclideanSpace.single i 1))) := by
  let v := matrixAction A.transpose w
  have hv : (∑ i : Fin n, v i • (EuclideanSpace.single i 1)) = v := by
    ext j
    simp [Pi.single_apply]
  change inner ℝ z (matrixAction A (matrixAction (coordinateHessian φ x) v)) = _
  conv_lhs => rw [← hv]
  simp only [map_sum, map_smul, inner_sum, real_inner_smul_right, v]

/-- The actual affine Stein identity at the original C1,1 source regularity.
 All global weak pairings are justified before expanding the finite sums. -/
theorem integral_linear_target_mul_test_eq_raw_C11
    {φ f : Space n → ℝ} {G : ℝ≥0} [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 1 φ) (hG : LipschitzWith G (gradient φ))
    (hiso : IsIsotropic (gradientPushforward φ))
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (A : Matrix (Fin n) (Fin n) ℝ) (w : Space n) :
    (∫ z, f z * inner ℝ z w ∂linearGradientPushforward φ A) =
      ∫ x, inner ℝ (gradient f (matrixAction A (gradient φ x)))
        (rawTransportedHessianDerivative φ A x w) ∂potentialMeasure φ := by
  let F := fun x => f (matrixAction A (gradient φ x))
  let v := matrixAction A.transpose w
  let R : Fin n → Space n → ℝ := fun i x =>
    inner ℝ (gradient f (matrixAction A (gradient φ x)))
      (matrixAction A (matrixAction (coordinateHessian φ x) (EuclideanSpace.single i 1)))
  have hF2 : MemLp F 2 (potentialMeasure φ) :=
    memLp_comp_linear_gradient_test_raw hG.continuous hf.continuous hc A 2
  have hg2 : MemLp (gradient φ) 2 (potentialMeasure φ) := by
    have hm := hiso.memLp_id
    change MemLp (fun x : Space n => x) 2 ((potentialMeasure φ).map (gradient φ)) at hm
    exact (memLp_map_measure_iff aestronglyMeasurable_id
      hG.continuous.measurable.aemeasurable).mp hm
  have hfd (i : Fin n) : Integrable (fun x => F x * coordinateDerivative φ i x)
      (potentialMeasure φ) := by
    convert hF2.integrable_mul (hg2.eval_piLp i) using 1
    funext x
    exact congrArg (fun t : ℝ => F x * t) (coordinateDerivative_eq_gradient φ i x)
  have hfp := memLp_comp_linear_gradient_test_gradient hG.continuous hf hc A
  have hRi (i : Fin n) : Integrable (R i) (potentialMeasure φ) := by
    have hh := (matrixAction A).comp_memLp'
      (memLp_matrixAction_actualHessian (μ := potentialMeasure φ) hG (EuclideanSpace.single i 1) 2)
    apply (hfp.norm.integrable_mul hh.norm).mono'
      (hfp.aestronglyMeasurable.inner hh.aestronglyMeasurable)
    exact Eventually.of_forall fun x => norm_inner_le_norm _ _
  have hmean (i : Fin n) : (∫ x, R i x ∂potentialMeasure φ) =
      ∫ x, F x * coordinateDerivative φ i x ∂potentialMeasure φ :=
    integral_raw_derivative_potential hφ (raw_linear_gradient_test_weak_derivative hφ hG hf A i)
      (hF2.integrable (by norm_num)) (hRi i) (hfd i)
  have hleft (x : Space n) :
      f (matrixAction A (gradient φ x)) * inner ℝ (matrixAction A (gradient φ x)) w =
        ∑ i, v i * (F x * coordinateDerivative φ i x) := by
    rw [inner_matrixAction_transpose]
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Finset.mul_sum,
      coordinateDerivative_eq_gradient, F, v]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [integral_linearGradientPushforward (g := fun z => f z * inner ℝ z w) hG.continuous
    (hf.continuous.mul (continuous_id.inner continuous_const)).measurable A]
  calc
    _ = ∫ x, ∑ i, v i * (F x * coordinateDerivative φ i x) ∂potentialMeasure φ :=
      integral_congr_ae (Eventually.of_forall hleft)
    _ = ∑ i, v i * ∫ x, F x * coordinateDerivative φ i x ∂potentialMeasure φ := by
      rw [integral_finsetSum _ (fun i _ => (hfd i).const_mul (v i))]
      simp only [integral_const_mul]
    _ = ∑ i, v i * ∫ x, R i x ∂potentialMeasure φ :=
      Finset.sum_congr rfl fun i _ => by rw [hmean i]
    _ = ∫ x, ∑ i, v i * R i x ∂potentialMeasure φ := by
      rw [integral_finsetSum _ (fun i _ => (hRi i).const_mul (v i))]
      simp only [integral_const_mul]
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x =>
        (inner_rawTransportedHessianDerivative_eq_sum φ A x w
          (gradient f (matrixAction A (gradient φ x)))).symm

theorem integral_linear_target_sq_le_raw_transported_energy_C11
    {φ f : Space n → ℝ} {G : ℝ≥0} [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 1 φ) (hG : LipschitzWith G (gradient φ))
    (hiso : IsIsotropic (gradientPushforward φ))
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (A : Matrix (Fin n) (Fin n) ℝ) (w : Space n) :
    (∫ z, f z * inner ℝ z w ∂linearGradientPushforward φ A) ^ 2 ≤
      (∫ x, ‖rawTransportedHessianDerivative φ A x w‖ ^ 2 ∂potentialMeasure φ) *
        ∫ z, ‖gradient f z‖ ^ 2 ∂linearGradientPushforward φ A := by
  rw [integral_linear_target_mul_test_eq_raw_C11 hφ hG hiso hf hc A w,
    integral_linearGradientPushforward hG.continuous ((measurable_gradient f).norm.pow_const 2),
    mul_comm]
  exact integral_inner_sq_le
    (memLp_comp_linear_gradient_test_gradient hG.continuous hf hc A)
    (memLp_rawTransportedHessianDerivative hG A w 2)

end MomentMap
end KLS
end

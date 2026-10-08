import KLS.MomentMapQuadraticVariance
import KLS.SteinMatrixContraction

/-!
# Actual affine transport of the moment-map Stein identity

The target is the actual image of the gradient law under a matrix. The Stein
derivative is transported on both sides: A (D grad phi) A-transpose. No
invertibility is required, and compact support is used only for the target
test, never for its pullback through a possibly singular map.
-/

open MeasureTheory ProbabilityTheory InnerProductSpace Matrix Set Filter
open scoped BigOperators ContDiff

noncomputable section
namespace KLS

variable {n : ℕ}

theorem inner_matrixAction_transpose (A : Matrix (Fin n) (Fin n) ℝ) (x y : Space n) :
    inner ℝ (matrixAction A x) y = inner ℝ x (matrixAction A.transpose y) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    matrixAction_apply, Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

namespace MomentMap

/-- The actual linear image of the moment-map target law. -/
def linearGradientPushforward (φ : Space n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    Measure (Space n) := (gradientPushforward φ).map (matrixAction A)

/-- The actual derivative transported on both sides, with the right-hand
factor being the transpose of the matrix used for the target law. -/
def transportedGradientDerivative (φ : Space n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (x w : Space n) : Space n :=
  matrixAction A (fderiv ℝ (gradient φ) x (matrixAction A.transpose w))


/-- The actual Hessian matrix represents the derivative of the gradient. -/
theorem matrixAction_hessianMatrix_apply {φ : Space n → ℝ}
    (hgrad : Differentiable ℝ (gradient φ)) (x v : Space n) :
    matrixAction (hessianMatrix φ x) v = fderiv ℝ (gradient φ) x v := by
  have hv : (∑ j : Fin n, v j • coordinateVector j) = v := by
    ext i
    simp [coordinateVector, WithLp.ofLp_sum, Finset.sum_apply, Pi.single_apply]
  calc
    matrixAction (hessianMatrix φ x) v =
        ∑ j : Fin n, v j • (fderiv ℝ (gradient φ) x (coordinateVector j)) := by
      ext i
      simp only [matrixAction_apply, WithLp.ofLp_sum, Finset.sum_apply,
        PiLp.smul_apply, smul_eq_mul, hessianMatrix_apply_eq hgrad]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = fderiv ℝ (gradient φ) x (∑ j : Fin n, v j • coordinateVector j) := by
      rw [map_sum]
      simp only [map_smul]
    _ = fderiv ℝ (gradient φ) x v := congrArg _ hv

theorem matrixAction_mul_apply (A D : Matrix (Fin n) (Fin n) ℝ) (v : Space n) :
    matrixAction (A * D) v = matrixAction A (matrixAction D v) := by
  ext i
  simp only [matrixAction_apply, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Identification with the literal congruence A H A-transpose used in the
finite matrix contraction. -/
theorem transportedGradientDerivative_eq_matrixAction {φ : Space n → ℝ}
    (hgrad : Differentiable ℝ (gradient φ))
    (A : Matrix (Fin n) (Fin n) ℝ) (x w : Space n) :
    transportedGradientDerivative φ A x w =
      matrixAction (A * hessianMatrix φ x * A.transpose) w := by
  rw [transportedGradientDerivative, ← matrixAction_hessianMatrix_apply hgrad]
  simp only [matrixAction_mul_apply]

/-- The exact noncommuting trace contraction at each source point. -/
theorem sum_transportedGradientDerivative_sq {φ : Space n → ℝ}
    (hgrad : Differentiable ℝ (gradient φ))
    (A U : Matrix (Fin n) (Fin n) ℝ) (x : Space n)
    (hH : (hessianMatrix φ x).IsSymm) (hU : U.transpose * U = 1) :
    (∑ i : Fin n, ‖transportedGradientDerivative φ A x (WithLp.toLp 2 (U i))‖ ^ 2) =
      (A.transpose * A * hessianMatrix φ x * (A.transpose * A) * hessianMatrix φ x).trace := by
  simp_rw [transportedGradientDerivative_eq_matrixAction hgrad]
  exact transported_stein_energy_contraction A (hessianMatrix φ x) U hH hU

instance isFiniteMeasure_linearGradientPushforward (φ : Space n → ℝ)
    [IsFiniteMeasure (potentialMeasure φ)] (A : Matrix (Fin n) (Fin n) ℝ) :
    IsFiniteMeasure (linearGradientPushforward φ A) := by
  unfold linearGradientPushforward gradientPushforward
  infer_instance

theorem integral_linearGradientPushforward {φ g : Space n → ℝ}
    (hgrad : Continuous (gradient φ)) (hg : Measurable g)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    (∫ z, g z ∂linearGradientPushforward φ A) =
      ∫ x, g (matrixAction A (gradient φ x)) ∂potentialMeasure φ := by
  rw [linearGradientPushforward,
    integral_map (matrixAction A).continuous.measurable.aemeasurable hg.aestronglyMeasurable,
    gradientPushforward, integral_map hgrad.measurable.aemeasurable
      (show AEStronglyMeasurable (fun x : Space n => g (matrixAction A x)) _ from
        (hg.comp (matrixAction A).continuous.measurable).aestronglyMeasurable)]

theorem fderiv_comp_linear_gradient_apply {φ f : Space n → ℝ}
    (hgrad : Differentiable ℝ (gradient φ)) (hf : Differentiable ℝ f)
    (A : Matrix (Fin n) (Fin n) ℝ) (x v : Space n) :
    fderiv ℝ (fun y => f (matrixAction A (gradient φ y))) x v =
      inner ℝ (gradient f (matrixAction A (gradient φ x)))
        (matrixAction A (fderiv ℝ (gradient φ) x v)) := by
  have hd := (hf (matrixAction A (gradient φ x))).hasFDerivAt.comp x
    ((matrixAction A).hasFDerivAt.comp x (hgrad x).hasFDerivAt)
  have hh := congrArg (fun L : Space n →L[ℝ] ℝ => L v) hd.fderiv
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, ← inner_gradient_left] using hh

theorem integrable_comp_linear_gradient_of_hasCompactSupport {φ f : Space n → ℝ}
    [IsFiniteMeasure (potentialMeasure φ)]
    (hgrad : Continuous (gradient φ)) (hf : Continuous f) (hc : HasCompactSupport f)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    Integrable (fun x => f (matrixAction A (gradient φ x))) (potentialMeasure φ) := by
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hf
  apply (integrable_const C).mono'
    (hf.comp ((matrixAction A).continuous.comp hgrad)).aestronglyMeasurable
  exact Eventually.of_forall fun x => hC (matrixAction A (gradient φ x))

theorem memLp_comp_linear_gradient_test_gradient {φ f : Space n → ℝ}
    [IsFiniteMeasure (potentialMeasure φ)]
    (hgrad : Continuous (gradient φ)) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    MemLp (fun x => gradient f (matrixAction A (gradient φ x))) 2 (potentialMeasure φ) := by
  obtain ⟨C, hC⟩ := (hc.fderiv ℝ).exists_bound_of_continuous
    (hf.fderiv_right (m := 0) (by norm_num)).continuous
  apply MemLp.of_bound ((measurable_gradient f).comp
    ((matrixAction A).continuous.comp hgrad).measurable).aestronglyMeasurable C
  exact Eventually.of_forall fun x => by
    simpa only [Function.comp_def, norm_gradient_eq_norm_fderiv] using hC (matrixAction A (gradient φ x))

theorem memLp_transportedGradientDerivative {φ : Space n → ℝ}
    [IsFiniteMeasure (potentialMeasure φ)] (hgrad : ContDiff ℝ 1 (gradient φ))
    {B : ℝ} (hB : ∀ x, ‖fderiv ℝ (gradient φ) x‖ ≤ B)
    (A : Matrix (Fin n) (Fin n) ℝ) (w : Space n) :
    MemLp (fun x => transportedGradientDerivative φ A x w) 2 (potentialMeasure φ) :=
  (matrixAction A).comp_memLp'
    (memLp_gradient_derivative_of_bound hgrad hB (matrixAction A.transpose w))

/-- The transported Stein identity for any matrix, with all L1 premises
derived from finite source mass, the actual derivative bound, and compact C1 tests. -/
theorem integral_linear_target_mul_test_eq {φ f : Space n → ℝ}
    [IsFiniteMeasure (potentialMeasure φ)]
    (hφ : Differentiable ℝ φ) (hgrad : ContDiff ℝ 1 (gradient φ))
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    {B : ℝ} (hB : ∀ x, ‖fderiv ℝ (gradient φ) x‖ ≤ B)
    (A : Matrix (Fin n) (Fin n) ℝ) (w : Space n) :
    (∫ z, f z * inner ℝ z w ∂linearGradientPushforward φ A) =
      ∫ x, inner ℝ (gradient f (matrixAction A (gradient φ x)))
        (transportedGradientDerivative φ A x w) ∂potentialMeasure φ := by
  let v := matrixAction A.transpose w
  let F := fun x => f (matrixAction A (gradient φ x))
  have hgD := hgrad.differentiable (by norm_num)
  have hfD := hf.differentiable (by norm_num)
  have hF : Differentiable ℝ F := hfD.comp ((matrixAction A).differentiable.comp hgD)
  have hFL1 : Integrable F (potentialMeasure φ) :=
    integrable_comp_linear_gradient_of_hasCompactSupport hgrad.continuous hf.continuous hc A
  have hfp := memLp_comp_linear_gradient_test_gradient hgrad.continuous hf hc A
  have hgp := memLp_transportedGradientDerivative hgrad hB A w
  have hdL1 : Integrable (fun x => inner ℝ (gradient f (matrixAction A (gradient φ x)))
      (transportedGradientDerivative φ A x w)) (potentialMeasure φ) := by
    apply (hfp.norm.integrable_mul hgp.norm).mono' (hfp.aestronglyMeasurable.inner hgp.aestronglyMeasurable)
    exact Eventually.of_forall fun x => norm_inner_le_norm _ _
  have hd : Integrable (fun x => fderiv ℝ F x v * (1 : ℝ)) (potentialMeasure φ) := by
    simpa only [F, v, mul_one, fderiv_comp_linear_gradient_apply hgD hfD,
      transportedGradientDerivative] using hdL1
  have hp : Integrable (fun x => F x * (1 : ℝ) * fderiv ℝ φ x v)
      (potentialMeasure φ) := by
    have hi := integrable_comp_linear_gradient_of_hasCompactSupport hgrad.continuous
      (hf.continuous.mul (continuous_id.inner (continuous_const (y := w)))) hc.mul_right A
    simpa only [Pi.mul_apply, id_eq, inner_matrixAction_transpose, inner_gradient_left,
      F, v, mul_one] using hi
  have hibp := integral_mul_fderiv_potentialMeasure hφ hF (differentiable_const (1 : ℝ)) v
    (by simpa only [mul_one] using hFL1) hd (by simp) hp
  simp only [fderiv_const_apply, _root_.zero_apply, mul_zero, integral_zero, mul_one,
    F, v, fderiv_comp_linear_gradient_apply hgD hfD, inner_gradient_left] at hibp
  rw [integral_linearGradientPushforward (g := fun z => f z * inner ℝ z w) hgrad.continuous
    (hf.continuous.mul (continuous_id.inner continuous_const)).measurable A]
  simp only [inner_matrixAction_transpose, inner_gradient_left, transportedGradientDerivative]
  linarith

/-- Cauchy--Schwarz with the correctly transported derivative energy. -/
theorem integral_linear_target_sq_le_transported_energy {φ f : Space n → ℝ}
    [IsFiniteMeasure (potentialMeasure φ)]
    (hφ : Differentiable ℝ φ) (hgrad : ContDiff ℝ 1 (gradient φ))
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    {B : ℝ} (hB : ∀ x, ‖fderiv ℝ (gradient φ) x‖ ≤ B)
    (A : Matrix (Fin n) (Fin n) ℝ) (w : Space n) :
    (∫ z, f z * inner ℝ z w ∂linearGradientPushforward φ A) ^ 2 ≤
      (∫ x, ‖transportedGradientDerivative φ A x w‖ ^ 2 ∂potentialMeasure φ) *
        (∫ z, ‖gradient f z‖ ^ 2 ∂linearGradientPushforward φ A) := by
  rw [integral_linear_target_mul_test_eq hφ hgrad hf hc hB A w,
    integral_linearGradientPushforward hgrad.continuous ((measurable_gradient f).norm.pow_const 2),
    mul_comm]
  exact integral_inner_sq_le
    (memLp_comp_linear_gradient_test_gradient hgrad.continuous hf hc A)
    (memLp_transportedGradientDerivative hgrad hB A w)

end MomentMap

/-- The actual transported Stein inequality supplies each quadratic derivative dual bound. -/
theorem quadratic_gradient_dual_of_linear_momentMap {φ V : Space n → ℝ}
    [IsFiniteMeasure (potentialMeasure φ)]
    (hφ : Differentiable ℝ φ) (hgrad : ContDiff ℝ 1 (gradient φ))
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hpush : MomentMap.linearGradientPushforward φ A = potentialMeasure V)
    {B : ℝ} (hB : ∀ x, ‖fderiv ℝ (gradient φ) x‖ ≤ B)
    (U : Matrix (Fin n) (Fin n) ℝ) (hU : U.IsSymm) (i : Fin n) :
    CoordinateGradientDualBound V (matrixQuadratic U) i
      (4 * ∫ x, ‖MomentMap.transportedGradientDerivative φ A x (WithLp.toLp 2 (U i))‖ ^ 2
        ∂potentialMeasure φ) := by
  intro h hh hc
  have hb := MomentMap.integral_linear_target_sq_le_transported_energy hφ hgrad hh hc hB A
    (WithLp.toLp 2 (U i))
  rw [hpush] at hb
  have heq : (∫ x, coordinateDerivative (matrixQuadratic U) i x * h x ∂potentialMeasure V) =
      2 * (∫ x, h x * inner ℝ x (WithLp.toLp 2 (U i)) ∂potentialMeasure V) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only
      rw [coordinateDerivative_matrixQuadratic U hU]
      ring
  rw [heq]
  nlinarith

/-- Quadratic variance controlled by the genuine transported contraction.
The target range-density premise and moment-map representation remain explicit. -/
theorem quadratic_variance_le_linear_momentMap_energy {φ V : Space n → ℝ}
    [IsFiniteMeasure (potentialMeasure φ)] [IsProbabilityMeasure (potentialMeasure V)]
    (hφ : Differentiable ℝ φ) (hgrad : ContDiff ℝ 1 (gradient φ))
    (hV : ContDiff ℝ 2 V) (hconv : ConvexOn ℝ univ V)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hpush : MomentMap.linearGradientPushforward φ A = potentialMeasure V)
    {B : ℝ} (hB : ∀ x, ‖fderiv ℝ (gradient φ) x‖ ≤ B)
    (U : Matrix (Fin n) (Fin n) ℝ) (hU : U.IsSymm)
    (hq : MemLp (matrixQuadratic U) 2 (potentialMeasure V))
    (hdense : DiffusionRangeDense V) :
    ProbabilityTheory.variance (matrixQuadratic U) (potentialMeasure V) ≤
      4 * ∑ i : Fin n,
        ∫ x, ‖MomentMap.transportedGradientDerivative φ A x (WithLp.toLp 2 (U i))‖ ^ 2
          ∂potentialMeasure φ := by
  rw [Finset.mul_sum]
  exact variance_le_sum_gradient_dual_of_rangeDense hV hconv
    ((contDiff_matrixQuadratic U).of_le (by simp)) hq
    (fun i => mul_nonneg (by norm_num) (integral_nonneg fun _ => sq_nonneg _))
    (quadratic_gradient_dual_of_linear_momentMap hφ hgrad A hpush hB U hU) hdense

end KLS
end

#print axioms KLS.MomentMap.integral_linear_target_mul_test_eq
#print axioms KLS.MomentMap.integral_linear_target_sq_le_transported_energy
#print axioms KLS.quadratic_gradient_dual_of_linear_momentMap
#print axioms KLS.quadratic_variance_le_linear_momentMap_energy

#print axioms KLS.MomentMap.transportedGradientDerivative_eq_matrixAction
#print axioms KLS.MomentMap.sum_transportedGradientDerivative_sq

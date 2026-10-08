import KLS.WeightedFlatnessIteration

open Matrix Set Filter Metric InnerProductSpace
open scoped Topology BigOperators Matrix.Norms.Elementwise
noncomputable section
namespace KLS
variable {n : ℕ}

lemma matrixAction_transpose_adjoint (A : Matrix (Fin n) (Fin n) ℝ) :
    matrixAction A.transpose = ContinuousLinearMap.adjoint (matrixAction A) := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  rw [inner_matrixAction_transpose, Matrix.transpose_transpose]

lemma norm_matrixAction_transpose (A : Matrix (Fin n) (Fin n) ℝ) :
    ‖matrixAction A.transpose‖ = ‖matrixAction A‖ := by
  rw [matrixAction_transpose_adjoint]
  exact ContinuousLinearMap.adjoint.norm_map A.toEuclideanLin.toContinuousLinearMap

lemma inverseSqrtMatrix_inverse_gram {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) :
    ((inverseSqrtMatrix A)⁻¹).transpose * (inverseSqrtMatrix A)⁻¹ = A := by
  let B := inverseSqrtMatrix A
  have hB : B.IsSymm := inverseSqrtMatrix_isSymm A
  have hdet : IsUnit B.det := isUnit_iff_ne_zero.mpr (inverseSqrtMatrix_det_ne_zero_of_posDef hA)
  have hwhite : B.transpose * A * B = 1 := by
    have hh := inverseSqrtMatrix_mul_self_mul_transpose hA
    change B * A * B.transpose = 1 at hh
    rw [hB.eq] at hh ⊢
    exact hh
  change B⁻¹.transpose * B⁻¹ = A
  calc
    _ = B⁻¹.transpose * (B.transpose * A * B) * B⁻¹ := by rw [hwhite, mul_one]
    _ = (B * B⁻¹).transpose * A * (B * B⁻¹) := by rw [Matrix.transpose_mul]; simp only [mul_assoc]
    _ = A := by rw [Matrix.mul_nonsing_inv B hdet, Matrix.transpose_one, one_mul, mul_one]

/-- The Hessian in the original coordinates associated with a cumulative
normalization frame. -/
def frameHessian (T : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  T⁻¹.transpose * T⁻¹

lemma frameHessian_posSemidef (T : Matrix (Fin n) (Fin n) ℝ) : (frameHessian T).PosSemidef := by
  simpa only [frameHessian, Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_conjTranspose_mul_self T⁻¹

lemma frameHessian_det_of_abs_det_one {T : Matrix (Fin n) (Fin n) ℝ} (hT : |T.det| = 1) :
    (frameHessian T).det = 1 := by
  have hsq : T.det ^ 2 = 1 := by nlinarith [sq_abs T.det]
  simp only [frameHessian, Matrix.det_mul, Matrix.det_transpose, Matrix.det_nonsing_inv]
  simp only [Ring.inverse_eq_inv, ← pow_two, inv_pow, hsq, inv_one]

lemma frameHessian_mul_inverseSqrtMatrix
    (T : Matrix (Fin n) (Fin n) ℝ) {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) :
    frameHessian (T * inverseSqrtMatrix A) = T⁻¹.transpose * A * T⁻¹ := by
  simp only [frameHessian, Matrix.mul_inv_rev, Matrix.transpose_mul]
  have hh := inverseSqrtMatrix_inverse_gram hA
  calc
    _ = T⁻¹.transpose * (((inverseSqrtMatrix A)⁻¹).transpose * (inverseSqrtMatrix A)⁻¹) * T⁻¹ := by
      simp only [mul_assoc]
    _ = _ := by rw [hh]

lemma frameHessian_increment
    (T : Matrix (Fin n) (Fin n) ℝ) {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) :
    frameHessian (T * inverseSqrtMatrix A) - frameHessian T =
      T⁻¹.transpose * (A - 1) * T⁻¹ := by
  rw [frameHessian_mul_inverseSqrtMatrix T hA, frameHessian, mul_sub, sub_mul, mul_one]

lemma norm_frameHessian_increment_le
    {T A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (hT : ‖matrixAction T⁻¹‖ ≤ 2)
    {η : ℝ} (hclose : ‖matrixAction (A - 1)‖ ≤ η) :
    ‖matrixAction (frameHessian (T * inverseSqrtMatrix A) - frameHessian T)‖ ≤ 4 * η := by
  have hη : 0 ≤ η := (norm_nonneg _).trans hclose
  rw [frameHessian_increment T hA]
  calc
    _ ≤ ‖matrixAction (T⁻¹.transpose * (A - 1))‖ * ‖matrixAction T⁻¹‖ := norm_matrixAction_mul_le _ _
    _ ≤ (‖matrixAction T⁻¹.transpose‖ * ‖matrixAction (A - 1)‖) * ‖matrixAction T⁻¹‖ :=
      mul_le_mul_of_nonneg_right (norm_matrixAction_mul_le _ _) (norm_nonneg _)
    _ = (‖matrixAction T⁻¹‖ * ‖matrixAction (A - 1)‖) * ‖matrixAction T⁻¹‖ := by rw [norm_matrixAction_transpose]
    _ ≤ (2 * η) * 2 := by gcongr
    _ = _ := by ring

end KLS
end

import KLS.TensorMatrixFamily

/-! The actual inverse-covariance tensor metric and its congruence invariance. -/
open Matrix
open scoped BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS.TensorEnergy
variable {n r : ℕ}

/-- The tensor metric is an actual quadratic form in full coordinate arrays. -/
def tensorMetric (A : Matrix (Fin n) (Fin n) ℝ) (T : (Fin r → Fin n) → ℝ) : ℝ :=
  T ⬝ᵥ (tensorMatrix A⁻¹ *ᵥ T)

theorem tensorMetric_one (T : (Fin r → Fin n) → ℝ) :
    tensorMetric 1 T = T ⬝ᵥ T := by
  simp [tensorMetric, tensorMatrix_one]

theorem inverse_congruence_cancel (A P : Matrix (Fin n) (Fin n) ℝ)
    (hP : P.det ≠ 0) : P * (P*A*P)⁻¹ * P = A⁻¹ := by
  have hu := isUnit_iff_ne_zero.mpr hP
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv P hu, Matrix.one_mul]
  rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul P hu, Matrix.mul_one]

theorem quadratic_congruence {ι : Type*} [Fintype ι]
    (Q R : Matrix ι ι ℝ) (T : ι → ℝ) :
    (Q *ᵥ T) ⬝ᵥ (R *ᵥ (Q *ᵥ T)) = T ⬝ᵥ ((Q.transpose * R * Q) *ᵥ T) := by
  calc
    _ = T ⬝ᵥ (Q.transpose *ᵥ (R *ᵥ (Q *ᵥ T))) := by
      rw [Matrix.dotProduct_transpose_mulVec, dotProduct_comm]
    _ = _ := by rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

/-- Paper (83), for every invertible symmetric change of coordinates. -/
theorem tensorMetric_congruence (A P : Matrix (Fin n) (Fin n) ℝ)
    (hPs : P.transpose = P) (hP : P.det ≠ 0) (T : (Fin r → Fin n) → ℝ) :
    tensorMetric (P*A*P) (tensorMatrix P *ᵥ T) = tensorMetric A T := by
  unfold tensorMetric
  rw [quadratic_congruence, ← tensorMatrix_transpose, hPs,
    ← tensorMatrix_mul, ← tensorMatrix_mul, inverse_congruence_cancel A P hP]

/-- When PAP=I, the inverse-covariance energy is the literal squared Euclidean
coordinate norm of the transformed tensor. -/
theorem tensorMetric_eq_whitened (A P : Matrix (Fin n) (Fin n) ℝ)
    (hPs : P.transpose = P) (hP : P.det ≠ 0) (hwhite : P*A*P = 1)
    (T : (Fin r → Fin n) → ℝ) :
    tensorMetric A T = (tensorMatrix P *ᵥ T) ⬝ᵥ (tensorMatrix P *ᵥ T) := by
  rw [← tensorMetric_congruence A P hPs hP T, hwhite, tensorMetric_one]

end KLS.TensorEnergy
end
#print axioms KLS.TensorEnergy.tensorMetric_congruence
#print axioms KLS.TensorEnergy.tensorMetric_eq_whitened

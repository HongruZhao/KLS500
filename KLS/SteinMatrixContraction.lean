import KLS.QuadraticEnergy
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# The matrix contraction after affine transport of a Stein kernel

The transported kernel is A H Aᵀ. Its squared Frobenius norm is the cyclic
contraction Tr(B H B H), where B = Aᵀ A. These are literal matrix identities;
no commutativity between H and B is imposed or inferred.
-/

open Matrix InnerProductSpace
open scoped BigOperators

noncomputable section
namespace KLS

variable {n : ℕ}

lemma matrixFrobeniusSq_eq_trace_mul_transpose (M : Matrix (Fin n) (Fin n) ℝ) :
    matrixFrobeniusSq M = (M * M.transpose).trace := by
  simp only [matrixFrobeniusSq, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.transpose_apply, pow_two]

lemma matrixFrobeniusSq_eq_trace_sq {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M.IsSymm) : matrixFrobeniusSq M = (M * M).trace := by
  rw [matrixFrobeniusSq_eq_trace_mul_transpose, hM.eq]

lemma matrixAction_row_eq_mul_transpose (M U : Matrix (Fin n) (Fin n) ℝ)
    (i : Fin n) :
    matrixAction M (WithLp.toLp 2 (U i)) = WithLp.toLp 2 (fun j => (M * U.transpose) j i) := by
  ext j
  rfl

/-- Summing the actual Euclidean squared norms over the rows of U gives the
squared Frobenius norm of the actual product M Uᵀ. -/
lemma sum_matrixAction_rows_norm_sq (M U : Matrix (Fin n) (Fin n) ℝ) :
    (∑ i : Fin n, ‖matrixAction M (WithLp.toLp 2 (U i))‖ ^ 2) =
      matrixFrobeniusSq (M * U.transpose) := by
  simp_rw [matrixAction_row_eq_mul_transpose, EuclideanSpace.real_norm_sq_eq]
  change (∑ i, ∑ j, (M * U.transpose) j i ^ 2) = _
  exact Finset.sum_comm

/-- Orthogonal changes of the test basis preserve the actual summed energy. -/
theorem sum_matrixAction_orthogonal_rows_norm_sq
    (M U : Matrix (Fin n) (Fin n) ℝ) (hU : U.transpose * U = 1) :
    (∑ i : Fin n, ‖matrixAction M (WithLp.toLp 2 (U i))‖ ^ 2) =
      matrixFrobeniusSq M := by
  rw [sum_matrixAction_rows_norm_sq, matrixFrobeniusSq_eq_trace_mul_transpose,
    matrixFrobeniusSq_eq_trace_mul_transpose, Matrix.transpose_mul,
    Matrix.transpose_transpose]
  congr 1
  calc
    M * U.transpose * (U * M.transpose) = M * (U.transpose * U) * M.transpose := by
      simp only [Matrix.mul_assoc]
    _ = M * M.transpose := by rw [hU, Matrix.mul_one]

/-- The transported Stein contraction has the noncommuting matrix order
needed by Letwin's estimate. -/
theorem matrixFrobeniusSq_affine_congruence
    (A H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) :
    matrixFrobeniusSq (A * H * A.transpose) =
      (A.transpose * A * H * (A.transpose * A) * H).trace := by
  have hs : (A * H * A.transpose).IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    have heq : (A * H * A.transpose).transpose = A * H * A.transpose := by
      rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hH.eq]
      simp only [Matrix.mul_assoc]
    exact congrArg (fun M => M i j) heq
  rw [matrixFrobeniusSq_eq_trace_sq hs]
  calc
    (A * H * A.transpose * (A * H * A.transpose)).trace =
        (A * (H * A.transpose * A * H * A.transpose)).trace := by
      simp only [Matrix.mul_assoc]
    _ = ((H * A.transpose * A * H * A.transpose) * A).trace := Matrix.trace_mul_comm _ _
    _ = ((H * (A.transpose * A) * H) * (A.transpose * A)).trace := by
      simp only [Matrix.mul_assoc]
    _ = ((A.transpose * A) * (H * (A.transpose * A) * H)).trace := Matrix.trace_mul_comm _ _
    _ = (A.transpose * A * H * (A.transpose * A) * H).trace := by
      simp only [Matrix.mul_assoc]

/-- Literal sum of transported coordinate energies, without substituting
the generally different contraction Tr(B² H²). -/
theorem transported_stein_energy_contraction
    (A H U : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm)
    (hU : U.transpose * U = 1) :
    (∑ i : Fin n,
      ‖matrixAction (A * H * A.transpose) (WithLp.toLp 2 (U i))‖ ^ 2) =
        (A.transpose * A * H * (A.transpose * A) * H).trace := by
  rw [sum_matrixAction_orthogonal_rows_norm_sq _ _ hU,
    matrixFrobeniusSq_affine_congruence A H hH]

end KLS
end

#print axioms KLS.sum_matrixAction_orthogonal_rows_norm_sq
#print axioms KLS.matrixFrobeniusSq_affine_congruence
#print axioms KLS.transported_stein_energy_contraction

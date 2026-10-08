import KLS.SteinMatrixContraction

/-!
# The normalized Hessian tensor comparison without diagonalizing B

For symmetric matrices B and T, the trace difference is half the squared
Frobenius norm of their commutator. Applying this to every slice of a
symmetric third-order tensor gives the normalized-Hessian comparison.
The general inverse-Hessian coordinate normalization remains separate.
-/

open Matrix
open scoped BigOperators

noncomputable section
namespace KLS

variable {n : ℕ}

lemma trace_abba_eq_aabb (B T : Matrix (Fin n) (Fin n) ℝ) :
    ((B * T) * (T * B)).trace = ((B * B) * (T * T)).trace := by
  calc
    ((B * T) * (T * B)).trace = (B * (T * T) * B).trace := by
      simp only [Matrix.mul_assoc]
    _ = (B * B * (T * T)).trace := Matrix.trace_mul_cycle _ _ _

lemma trace_baba_eq_abab (B T : Matrix (Fin n) (Fin n) ℝ) :
    ((T * B) * (T * B)).trace = ((B * T) * (B * T)).trace := by
  calc
    ((T * B) * (T * B)).trace = (T * (B * T * B)).trace := by
      simp only [Matrix.mul_assoc]
    _ = ((B * T * B) * T).trace := Matrix.trace_mul_comm _ _
    _ = ((B * T) * (B * T)).trace := by simp only [Matrix.mul_assoc]

/-- The commutator sum of squares keeps the exact noncommuting order. -/
theorem matrix_trace_commutator_difference
    (B T : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm) (hT : T.IsSymm) :
    ((B * B) * (T * T)).trace - ((B * T) * (B * T)).trace =
      (1 / 2 : ℝ) * matrixFrobeniusSq (B * T - T * B) := by
  rw [matrixFrobeniusSq_eq_trace_mul_transpose, Matrix.transpose_sub,
    Matrix.transpose_mul, Matrix.transpose_mul, hB.eq, hT.eq,
    Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.trace_sub,
    Matrix.trace_sub, Matrix.trace_sub]
  rw [trace_abba_eq_aabb B T, trace_abba_eq_aabb T B,
    trace_baba_eq_abab B T, Matrix.trace_mul_comm (T * T) (B * B)]
  ring

theorem matrix_trace_cross_le_square
    (B T : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm) (hT : T.IsSymm) :
    ((B * T) * (B * T)).trace ≤ ((B * B) * (T * T)).trace := by
  have hn : 0 ≤ matrixFrobeniusSq (B * T - T * B) := by
    unfold matrixFrobeniusSq
    positivity
  have heq := matrix_trace_commutator_difference B T hB hT
  linarith

/-- The comparison holds for every actual symmetric slice, with no
diagonalization premise or sign restriction on the symmetric B. -/
theorem sum_matrix_trace_cross_le_square
    {κ : Type*} [Fintype κ] (B : Matrix (Fin n) (Fin n) ℝ)
    (T : κ → Matrix (Fin n) (Fin n) ℝ)
    (hB : B.IsSymm) (hT : ∀ k, (T k).IsSymm) :
    (∑ k, ((B * T k) * (B * T k)).trace) ≤
      ∑ k, ((B * B) * (T k * T k)).trace :=
  Finset.sum_le_sum fun k _ => matrix_trace_cross_le_square B (T k) hB (hT k)

/-- The third-order Gram contraction equals the sum of matrix-square
contractions by full tensor symmetry. No basis is chosen. -/
lemma tensor_gram_contraction_eq_trace_square
    (B : Matrix (Fin n) (Fin n) ℝ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hfirst : ∀ i j k, T i j k = T j i k)
    (hlast : ∀ i j k, T i j k = T i k j) :
    (∑ i, ∑ j, (B * B) i j * (T i * T j).trace) =
      ∑ k, ((B * B) * (T k * T k)).trace := by
  have hcycle (k a i : Fin n) : T k a i = T i a k := by
    rw [hfirst k a i, hlast a k i, hfirst a i k]
  change (∑ i, ∑ j, (B * B) i j * (∑ a, ∑ b, T i a b * T j b a)) =
    ∑ a, ∑ i, ∑ j, (B * B) i j * (∑ b, T a j b * T a b i)
  simp only [Finset.mul_sum]
  conv_rhs =>
    rw [Finset.sum_comm]
    arg 2
    ext i
    rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [hfirst a j b, hcycle a b i, hlast j a b, hlast i a b]
  ring

/-- Letwin's normalized-Hessian comparison for an arbitrary symmetric B.
Full tensor symmetry, not diagonal coordinates, identifies the Gram side. -/
theorem normalized_tensor_trace_comparison
    (B : Matrix (Fin n) (Fin n) ℝ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hB : B.IsSymm)
    (hfirst : ∀ i j k, T i j k = T j i k)
    (hlast : ∀ i j k, T i j k = T i k j) :
    (∑ k, ((B * T k) * (B * T k)).trace) ≤
      ∑ i, ∑ j, (B * B) i j * (T i * T j).trace := by
  rw [tensor_gram_contraction_eq_trace_square B T hfirst hlast]
  exact sum_matrix_trace_cross_le_square B T hB
    (fun k => Matrix.IsSymm.ext (fun i j => (hlast k i j).symm))

end KLS
end

#print axioms KLS.matrix_trace_commutator_difference
#print axioms KLS.sum_matrix_trace_cross_le_square
#print axioms KLS.normalized_tensor_trace_comparison

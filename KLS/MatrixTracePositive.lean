import KLS.HessianMetricEvolution
import Mathlib.Analysis.Matrix.Order

/-!
# Positive trace contractions and weighted matrix Gram forms

The weighted Gram matrix is a congruence of the genuine Kronecker product.
This proves positivity without choosing or assuming a diagonal basis.
-/

open Matrix
open scoped BigOperators Kronecker

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS

variable {n : ℕ}

lemma matrix_entrywise_contraction_eq_trace
    (A B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm) :
    (∑ i, ∑ j, A i j * B i j) = (A * B).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hB.apply i j]

/-- The trace of the product of two PSD matrices is nonnegative, without
asserting that the generally noncommuting product is itself PSD. -/
theorem trace_mul_nonneg_of_posSemidef {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (A * B).trace := by
  rw [← matrix_entrywise_contraction_eq_trace A B hB.isHermitian.isSymm]
  have hp := (hA.hadamard hB).dotProduct_mulVec_nonneg (fun _ => (1 : ℝ))
  simpa only [dotProduct, Matrix.mulVec, Matrix.hadamard_apply, star_trivial,
    Pi.mul_apply, one_mul, mul_one] using hp

def matrixTraceGram (P : Matrix (Fin n) (Fin n) ℝ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (P * T i * P * T j).trace

def matrixFamilyColumns (T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n × Fin n) (Fin n) ℝ := fun p i => T i p.1 p.2

lemma matrixTraceGram_eq_kronecker_congruence
    (P : Matrix (Fin n) (Fin n) ℝ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hP : P.IsSymm) (hT : ∀ i, (T i).IsSymm) :
    matrixTraceGram P T =
      (matrixFamilyColumns T)ᴴ *
        (P ⊗ₖ P) * (matrixFamilyColumns T) := by
  ext i j
  rw [matrixTraceGram, trace_inverse_hessian_contraction P (T i) (T j) hP (hT j)]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial, matrixFamilyColumns,
    Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  simp only [Fintype.sum_prod_type, Matrix.kroneckerMap_apply]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  ring

/-- The actual weighted Gram matrix is PSD for every symmetric family. -/
theorem matrixTraceGram_posSemidef
    {P : Matrix (Fin n) (Fin n) ℝ} (hP : P.PosSemidef)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm) :
    (matrixTraceGram P T).PosSemidef := by
  rw [matrixTraceGram_eq_kronecker_congruence P T hP.isHermitian.isSymm hT]
  exact (hP.kronecker hP).conjTranspose_mul_mul_same _

theorem inverse_weighted_traceGram_nonneg
    {J B : Matrix (Fin n) (Fin n) ℝ} (hJ : J.PosSemidef) (hB : B.PosSemidef)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm) :
    0 ≤ ∑ i, ∑ j, J i j * (B * T i * B * T j).trace := by
  have hQ := matrixTraceGram_posSemidef hB T hT
  change 0 ≤ ∑ i, ∑ j, J i j * matrixTraceGram B T i j
  rw [matrix_entrywise_contraction_eq_trace J _ hQ.isHermitian.isSymm]
  exact trace_mul_nonneg_of_posSemidef hJ hQ

end KLS
end

#print axioms KLS.trace_mul_nonneg_of_posSemidef
#print axioms KLS.matrixTraceGram_posSemidef
#print axioms KLS.inverse_weighted_traceGram_nonneg

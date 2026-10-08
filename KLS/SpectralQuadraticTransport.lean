import KLS.SteinMatrixContraction
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Actual spectral transport of a symmetric quadratic

A symmetric matrix M admits actual symmetric matrices A, U and B such that
Aᵀ U A = M, Uᵀ U = I, Aᵀ A = B, and B has the same squared Frobenius norm
as M. The construction uses sqrt(abs(lambda)) and an orthogonal sign choice
on each eigenspace. At a zero eigenvalue that sign is chosen to be one.
-/

open Matrix Unitary
open scoped BigOperators

noncomputable section
namespace KLS

variable {n : ℕ}

def orthogonalScalarSign (t : ℝ) : ℝ := if t < 0 then -1 else 1

lemma orthogonalScalarSign_sq (t : ℝ) : orthogonalScalarSign t ^ 2 = 1 := by
  unfold orthogonalScalarSign
  split_ifs <;> norm_num

lemma sqrt_abs_sign_sqrt_abs (t : ℝ) :
    Real.sqrt |t| * orthogonalScalarSign t * Real.sqrt |t| = t := by
  have hs := Real.sq_sqrt (abs_nonneg t)
  unfold orthogonalScalarSign
  split_ifs with ht
  · rw [abs_of_neg ht] at hs ⊢
    nlinarith
  · rw [abs_of_nonneg (le_of_not_gt ht)] at hs ⊢
    nlinarith

lemma isSymm_unitary_conj_diagonal
    (Q : unitary (Matrix (Fin n) (Fin n) ℝ)) (v : Fin n → ℝ) :
    (conjStarAlgAut ℝ _ Q (Matrix.diagonal v)).IsSymm := by
  exact ((Matrix.isHermitian_iff_isSymm.mpr (Matrix.isSymm_diagonal v)).isSelfAdjoint.map
    (conjStarAlgAut ℝ _ Q)).isHermitian.isSymm

lemma trace_unitary_conj (Q : unitary (Matrix (Fin n) (Fin n) ℝ))
    (M : Matrix (Fin n) (Fin n) ℝ) :
    (conjStarAlgAut ℝ _ Q M).trace = M.trace := by
  rw [conjStarAlgAut_apply, Matrix.trace_mul_cycle, Unitary.coe_star_mul_self,
    Matrix.one_mul]

/-- The explicit finite spectral construction, valid even for singular M.
For a density transport one still needs A invertible; this theorem makes no
claim that a singular pushforward has a full-dimensional density. -/
theorem exists_spectral_quadratic_transport (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M.IsSymm) :
    ∃ A U B : Matrix (Fin n) (Fin n) ℝ,
      A.IsSymm ∧ U.IsSymm ∧ B.IsSymm ∧
      U.transpose * U = 1 ∧ A.transpose * A = B ∧
      A.transpose * U * A = M ∧ matrixFrobeniusSq B = matrixFrobeniusSq M := by
  let hH : M.IsHermitian := Matrix.isHermitian_iff_isSymm.mpr hM
  let e := conjStarAlgAut ℝ _ hH.eigenvectorUnitary
  let a : Fin n → ℝ := fun i => Real.sqrt |hH.eigenvalues i|
  let u : Fin n → ℝ := fun i => orthogonalScalarSign (hH.eigenvalues i)
  let b : Fin n → ℝ := fun i => |hH.eigenvalues i|
  let A := e (diagonal a)
  let U := e (diagonal u)
  let B := e (diagonal b)
  have hA : A.IsSymm := isSymm_unitary_conj_diagonal _ a
  have hU : U.IsSymm := isSymm_unitary_conj_diagonal _ u
  have hB : B.IsSymm := isSymm_unitary_conj_diagonal _ b
  have hspec : M = e (diagonal hH.eigenvalues) := by
    simpa only [Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using hH.spectral_theorem
  refine ⟨A, U, B, hA, hU, hB, ?_, ?_, ?_, ?_⟩
  · rw [hU.eq]
    change e (diagonal u) * e (diagonal u) = 1
    rw [← map_mul, Matrix.diagonal_mul_diagonal]
    have hd : (fun i => u i * u i) = fun _ => (1 : ℝ) := by
      funext i
      exact (pow_two (u i)).symm.trans (orthogonalScalarSign_sq _)
    rw [hd, Matrix.diagonal_one, map_one]
  · rw [hA.eq]
    change e (diagonal a) * e (diagonal a) = e (diagonal b)
    rw [← map_mul, Matrix.diagonal_mul_diagonal]
    congr 2
    funext i
    exact Real.mul_self_sqrt (abs_nonneg _)
  · rw [hA.eq, hspec]
    change e (diagonal a) * e (diagonal u) * e (diagonal a) = e (diagonal hH.eigenvalues)
    rw [← map_mul, ← map_mul, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 2
    funext i
    exact sqrt_abs_sign_sqrt_abs _
  · rw [matrixFrobeniusSq_eq_trace_sq hB, matrixFrobeniusSq_eq_trace_sq hM, hspec]
    change (e (diagonal b) * e (diagonal b)).trace =
      (e (diagonal hH.eigenvalues) * e (diagonal hH.eigenvalues)).trace
    rw [← map_mul, ← map_mul, trace_unitary_conj, trace_unitary_conj,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 2
    funext i
    dsimp [b]
    nlinarith [sq_abs (hH.eigenvalues i)]

end KLS
end

#print axioms KLS.exists_spectral_quadratic_transport

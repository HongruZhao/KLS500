import KLS.SpectralQuadraticTransport

/-! # An actual symmetric square root of every real PSD matrix -/

open Matrix Unitary
open scoped BigOperators

noncomputable section
namespace KLS

variable {n : ℕ}

/-- The square root is constructed from the genuine spectral decomposition.
No factorization or choice of diagonal coordinates is assumed. -/
theorem exists_symmetric_matrix_square_root
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.PosSemidef) :
    ∃ R : Matrix (Fin n) (Fin n) ℝ, R.IsSymm ∧ R.transpose * R = B := by
  let e := conjStarAlgAut ℝ _ hB.isHermitian.eigenvectorUnitary
  let r : Fin n → ℝ := fun i => Real.sqrt (hB.isHermitian.eigenvalues i)
  let R := e (diagonal r)
  have hR : R.IsSymm := isSymm_unitary_conj_diagonal _ r
  have hspec : B = e (diagonal hB.isHermitian.eigenvalues) := by
    simpa only [Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using hB.isHermitian.spectral_theorem
  refine ⟨R, hR, ?_⟩
  rw [hR.eq, hspec]
  change e (diagonal r) * e (diagonal r) = e (diagonal hB.isHermitian.eigenvalues)
  rw [← map_mul, Matrix.diagonal_mul_diagonal]
  congr 2
  funext i
  exact Real.mul_self_sqrt (hB.eigenvalues_nonneg i)

end KLS
end

#print axioms KLS.exists_symmetric_matrix_square_root

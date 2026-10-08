import KLS.PositiveMatrixSquareRoot
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! The actual supporting-hyperplane inequality for log determinant on
positive-definite real matrices. The reduction uses a constructed symmetric
square root of the inverse, so no simultaneous diagonalization is assumed. -/

open Matrix
open scoped BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

theorem log_det_le_trace_sub_dimension {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) : Real.log A.det ≤ A.trace - n := by
  rw [hA.isHermitian.det_eq_prod_eigenvalues,
    hA.isHermitian.trace_eq_sum_eigenvalues]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  rw [Real.log_prod (fun i _ => (hA.eigenvalues_pos i).ne')]
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => Real.log_le_sub_one_of_pos (hA.eigenvalues_pos i))
  simpa only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] using h

theorem log_det_tangent_bound {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) (hB : B.PosDef) :
    Real.log B.det ≤ Real.log A.det + (A⁻¹ * B).trace - n := by
  obtain ⟨R, hR, hRR⟩ := exists_symmetric_matrix_square_root hA.inv.posSemidef
  have hRR' : R * R = A⁻¹ := by simpa only [hR.eq] using hRR
  have hRdet : R.det ≠ 0 := by
    intro hz
    have h := congrArg Matrix.det hRR'
    rw [Matrix.det_mul, hz, zero_mul] at h
    exact hA.inv.det_pos.ne' h.symm
  have hRu : IsUnit R := (Matrix.isUnit_iff_isUnit_det _).mpr
    (isUnit_iff_ne_zero.mpr hRdet)
  let C := R * B * R
  have hC : C.PosDef := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
      hR.eq] using (hRu.posDef_star_left_conjugate_iff).mpr hB
  have hdet : C.det = (A⁻¹).det * B.det := by
    have h := congrArg Matrix.det hRR'
    rw [Matrix.det_mul] at h
    dsimp [C]
    rw [Matrix.det_mul, Matrix.det_mul, ← h]
    ring
  have htrace : C.trace = (A⁻¹ * B).trace := by
    dsimp [C]
    rw [Matrix.trace_mul_cycle, hRR']
  have hlog : Real.log C.det = -Real.log A.det + Real.log B.det := by
    rw [hdet, Real.log_mul hA.inv.det_pos.ne' hB.det_pos.ne',
      Matrix.det_nonsing_inv, Ring.inverse_eq_inv, Real.log_inv]
  have h := log_det_le_trace_sub_dimension hC
  rw [hlog, htrace] at h
  linarith

end KLS
end

#print axioms KLS.log_det_le_trace_sub_dimension
#print axioms KLS.log_det_tangent_bound

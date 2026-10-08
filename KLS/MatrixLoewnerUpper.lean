import KLS.MatrixOperatorEntryBound
import KLS.PositiveMatrixPerturbation

open Matrix InnerProductSpace
open scoped BigOperators Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- A bound on the genuine Euclidean matrix action gives the exact Loewner
upper bound for every symmetric matrix. -/
theorem loewner_upper_of_matrixAction_norm_le {H : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.IsSymm) {K : ℝ} (hK : ‖matrixAction H‖ ≤ K) :
    (K • (1 : Matrix (Fin n) (Fin n) ℝ) - H).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact (Matrix.isHermitian_one.smul (IsSelfAdjoint.all K)).sub
      (Matrix.isHermitian_iff_isSymm.mpr hH)
  intro w
  let x : Space n := WithLp.toLp 2 w
  have hu : inner ℝ x (matrixAction H x) ≤ K * ‖x‖ ^ 2 := by
    calc
      _ ≤ ‖x‖ * ‖matrixAction H x‖ := real_inner_le_norm _ _
      _ ≤ ‖x‖ * (‖matrixAction H‖ * ‖x‖) :=
        mul_le_mul_of_nonneg_left ((matrixAction H).le_opNorm x) (norm_nonneg _)
      _ ≤ ‖x‖ * (K * ‖x‖) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hK (norm_nonneg _)) (norm_nonneg _)
      _ = _ := by ring
  have hp : 0 ≤ inner ℝ x (matrixAction (K • (1 : Matrix (Fin n) (Fin n) ℝ) - H) x) := by
    rw [matrixAction_sub_matrices, matrixAction_smul_scalar, matrixAction_one_apply,
      inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq]
    exact sub_nonneg.mpr hu
  simpa only [x, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    dotProduct, Matrix.mulVec, matrixAction_apply, star_trivial, mul_comm] using hp

/-- A coarse explicit positive bound suffices when only the actual
entrywise matrix norm is available, including dimension zero. -/
theorem loewner_upper_of_elementwise_norm_le {H : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.IsSymm) {L : ℝ} (hL : ‖H‖ ≤ L) :
    (((n : ℝ) ^ 2 * L + 1) • (1 : Matrix (Fin n) (Fin n) ℝ) - H).PosSemidef := by
  have hLn : 0 ≤ L := (norm_nonneg H).trans hL
  have hb := norm_matrixAction_le_of_entries_le hLn ((Matrix.norm_le_iff hLn).mp hL)
  exact loewner_upper_of_matrixAction_norm_le hH (hb.trans (by linarith))

end KLS
end

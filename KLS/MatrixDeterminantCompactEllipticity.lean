import KLS.CompactPositiveMatrixField
import Mathlib.Analysis.Matrix.Order

open Matrix Set Metric InnerProductSpace
open scoped Topology Matrix.Norms.Elementwise
noncomputable section
namespace KLS
variable {n : ℕ}

/-- Fixed positive determinant and finite entry bounds make the entire
semidefinite matrix class uniformly positive. The lower constant depends only
on dimension, the entry bound, and the determinant lower bound. -/
theorem exists_uniform_ellipticity_of_det_and_norm
    (n : ℕ) (M d : ℝ) (hd : 0 < d) :
    ∃ μ Λ : ℝ, 0 < μ ∧ 0 < Λ ∧
      ∀ A : Matrix (Fin n) (Fin n) ℝ, A.PosSemidef → ‖A‖ ≤ M → d ≤ A.det →
        ∀ v : Space n, μ * ‖v‖^2 ≤ inner ℝ v (matrixAction A v) ∧
          inner ℝ v (matrixAction A v) ≤ Λ * ‖v‖^2 := by
  let S : Set (Matrix (Fin n) (Fin n) ℝ) :=
    closedBall 0 M ∩ {A | A.PosSemidef} ∩ {A | d ≤ A.det}
  have hS : IsCompact S :=
    ((isCompact_closedBall 0 M).inter_right Matrix.posSemidef_is_closed).inter_right
      (isClosed_le continuous_const continuous_id.matrix_det)
  have hpos (A : Matrix (Fin n) (Fin n) ℝ) (hA : A ∈ S) : A.PosDef :=
    hA.1.2.posDef_iff_det_ne_zero.mpr ((hd.trans_le hA.2).ne')
  obtain ⟨μ,Λ,hμ,hΛ,hbounds⟩ := compact_positive_matrix_uniform_ellipticity
    (A := fun A : Matrix (Fin n) (Fin n) ℝ => A) hS continuous_id.continuousOn hpos
  refine ⟨μ,Λ,hμ,hΛ,?_⟩
  intro A hA hM hdet v
  exact hbounds A ⟨⟨by simpa using hM,hA⟩,hdet⟩ v

end KLS
end

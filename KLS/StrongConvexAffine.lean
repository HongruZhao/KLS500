import KLS.AffinePotentialCutoff
import Mathlib.Analysis.Convex.Strong

/-! Strong convexity survives the actual invertible affine change of
variables, with an explicit positive loss controlled by the forward map. -/

open MeasureTheory Set Matrix
open scoped ContDiff

noncomputable section
namespace KLS

lemma strongConvexOn_add_const {n : ℕ} {V : Space n → ℝ} {κ : ℝ}
    (hV : StrongConvexOn univ κ V) (c : ℝ) :
    StrongConvexOn univ κ (fun x => V x + c) := by
  rw [strongConvexOn_iff_convex] at hV ⊢
  convert hV.add_const c using 1
  ext x
  dsimp
  ring

lemma strongConvexOn_add_norm_sq {n : ℕ} {V : Space n → ℝ}
    (hV : ConvexOn ℝ univ V) (ε : ℝ) :
    StrongConvexOn univ (2 * ε) (fun x => V x + ε * ‖x‖ ^ 2) := by
  rw [strongConvexOn_iff_convex]
  convert hV using 1
  ext x
  ring

/-- The reciprocal affine map loses at most the square of this explicit
positive upper bound for the norm of the forward linear map. -/
lemma affineTransformedPotential_strongConvex {n : ℕ} {V : Space n → ℝ}
    {κ : ℝ} (hκ : 0 ≤ κ) (hV : StrongConvexOn univ κ V)
    (A : Matrix (Fin n) (Fin n) ℝ) (b : Space n) (hA : A.det ≠ 0) :
    StrongConvexOn univ (κ / (‖matrixAction A‖ + 1) ^ 2)
      (affineTransformedPotential V A b hA) := by
  let e := affineMatrixEquiv A b hA
  let C : ℝ := ‖matrixAction A‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hbound (x y : Space n) : ‖x - y‖ ≤ C * ‖e.symm x - e.symm y‖ := by
    have heq : x - y = matrixAction A (e.symm x - e.symm y) := by
      have hx := e.apply_symm_apply x
      have hy := e.apply_symm_apply y
      change matrixAction A (e.symm x) + b = x at hx
      change matrixAction A (e.symm y) + b = y at hy
      calc
        x - y = (matrixAction A (e.symm x) + b) -
            (matrixAction A (e.symm y) + b) := congrArg₂ (· - ·) hx.symm hy.symm
        _ = matrixAction A (e.symm x - e.symm y) := by rw [map_sub]; abel
    rw [heq]
    exact ((matrixAction A).le_opNorm _).trans (by
      dsimp [C]
      nlinarith [norm_nonneg (e.symm x - e.symm y)])
  have hcomp : StrongConvexOn univ (κ / C ^ 2) (fun x => V (e.symm x)) := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    have hh := hV.2 (mem_univ (e.symm x)) (mem_univ (e.symm y)) ha hb hab
    have heq : e.symm (a • x + b • y) = a • e.symm x + b • e.symm y := by
      exact Convex.combo_affine_apply (f := e.symm.toAffineEquiv.toAffineMap) hab
    dsimp only
    rw [heq]
    apply hh.trans
    have hsq : ‖x - y‖ ^ 2 ≤ C ^ 2 * ‖e.symm x - e.symm y‖ ^ 2 := by
      nlinarith [hbound x y, norm_nonneg (x - y),
        norm_nonneg (e.symm x - e.symm y)]
    have hdiv : κ / C ^ 2 * ‖x - y‖ ^ 2 ≤ κ * ‖e.symm x - e.symm y‖ ^ 2 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (sq_pos_of_pos hC)]
      nlinarith [mul_le_mul_of_nonneg_left hsq hκ]
    simp only [smul_eq_mul]
    nlinarith [mul_le_mul_of_nonneg_left hdiv (mul_nonneg ha hb)]
  convert strongConvexOn_add_const hcomp (-Real.log |A.det⁻¹|) using 1
  ext x
  exact sub_eq_add_neg _ _

end KLS
end

#print axioms KLS.affineTransformedPotential_strongConvex

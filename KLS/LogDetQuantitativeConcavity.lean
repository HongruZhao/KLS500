import KLS.MatrixInverseCoercivity
import KLS.LogDetLineDerivatives
import Mathlib.Analysis.Convex.Deriv

open Matrix Set
open scoped BigOperators Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- Quantitative log-det concavity on positive matrices bounded above by K.
The complete ordered-entry Frobenius gap is derived from the actual second
variation along the matrix segment. -/
theorem log_det_tangent_frobenius_gap {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) (hB : B.PosDef) {K : ℝ} (hK : 0 < K)
    (hAu : (K • (1 : Matrix (Fin n) (Fin n) ℝ) - A).PosSemidef)
    (hBu : (K • (1 : Matrix (Fin n) (Fin n) ℝ) - B).PosSemidef) :
    Real.log B.det + ((K⁻¹) ^ 2 / 2) * matrixFrobeniusSq (B - A) ≤
      Real.log A.det + (A⁻¹ * (B - A)).trace := by
  let D := B - A
  let C (t : ℝ) := A + t • D
  let c : ℝ := (K⁻¹) ^ 2 * matrixFrobeniusSq D
  let q (t : ℝ) := ((C t)⁻¹ * D).trace
  let g (t : ℝ) := -Real.log (C t).det - (c / 2) * t ^ 2
  let g' (t : ℝ) := -q t - c * t
  let g'' (t : ℝ) := ((C t)⁻¹ * D * (C t)⁻¹ * D).trace - c
  have hD : D.IsSymm := hB.isHermitian.isSymm.sub hA.isHermitian.isSymm
  have hCd (t : ℝ) : HasDerivAt C D t := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id t).smul_const D).const_add A
  have hCp (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : (C t).PosDef := by
    by_cases ht1 : t = 1
    · simpa only [ht1, C, D, one_smul, add_sub_cancel] using hB
    · have hlt : 0 < 1 - t := sub_pos.mpr ((lt_or_eq_of_le ht.2).resolve_right ht1)
      convert (hA.smul hlt).add_posSemidef (hB.posSemidef.smul ht.1) using 1
      dsimp only [C, D]
      module
  have hCu (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (K • (1 : Matrix (Fin n) (Fin n) ℝ) - C t).PosSemidef := by
    convert (hAu.smul (sub_nonneg.mpr ht.2)).add (hBu.smul ht.1) using 1
    dsimp only [C, D]
    module
  have hlog (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun s => Real.log (C s).det) (q t) t :=
    hasDerivAt_matrix_logDet (hCd t) (hCp t ht).det_pos.ne'
  have hq (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt q (-((C t)⁻¹ * D * (C t)⁻¹ * D).trace) t :=
    hasDerivAt_trace_matrix_inv_mul (hCd t) (hCp t ht).det_pos.ne' D
  have hg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt g (g' t) t := by
    convert (hlog t ht).neg.sub (((hasDerivAt_id t).pow 2).const_mul (c / 2)) using 1
    · rfl
    · dsimp [g']
      ring
  have hg' (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt g' (g'' t) t := by
    convert (hq t ht).neg.sub ((hasDerivAt_id t).const_mul c) using 1
    · rfl
    · dsimp [g'']
      ring
  have hnonneg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : 0 ≤ g'' t := by
    exact sub_nonneg.mpr (inverse_trace_square_lower_of_upper (hCp t ht) hK (hCu t ht) hD)
  have hconv : ConvexOn ℝ (Icc (0 : ℝ) 1) g :=
    convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
      (fun t ht => (hg t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hg t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht => (hg' t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht => hnonneg t (interior_subset ht))
  have hsec := hconv.le_slope_of_hasDerivAt (x := 0) (y := 1) (by simp) (by simp) (by norm_num)
    (hg 0 (by simp))
  norm_num [slope, g, g', q, C, D] at hsec
  dsimp [c, D] at hsec
  linarith

end KLS
end

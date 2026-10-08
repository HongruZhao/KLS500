import KLS.WeightedWhiteningRegularity

open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff NNReal ENNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

lemma map_potentialMeasure_matrix_with_jacobian
    {W : Space n → ℝ} (hW : Measurable W)
    (B : Matrix (Fin n) (Fin n) ℝ) (hne : B.det ≠ 0) :
    (potentialMeasure W).map (affineMatrixEquiv B 0 hne) =
      potentialMeasure (fun q => W ((affineMatrixEquiv B 0 hne).symm q) + Real.log |B.det|) := by
  rw [map_potentialMeasure_affineMatrixEquiv hW]
  congr 1
  funext q
  change W ((affineMatrixEquiv B 0 hne).symm q) - Real.log |B.det⁻¹| = _
  rw [abs_inv, Real.log_inv]
  ring

lemma map_potentialMeasure_inverse_matrix_with_jacobian
    {W : Space n → ℝ} (hW : Measurable W)
    (B : Matrix (Fin n) (Fin n) ℝ) (hne : B.det ≠ 0) :
    (potentialMeasure W).map (affineMatrixEquiv B 0 hne).symm =
      potentialMeasure (fun y => W (matrixAction B y) - Real.log |B.det|) := by
  let e := affineMatrixEquiv B 0 hne
  let S : Space n → ℝ := fun y => W (matrixAction B y) - Real.log |B.det|
  have hS : Measurable S := (hW.comp (matrixAction B).continuous.measurable).sub_const _
  have hm : (potentialMeasure S).map e = potentialMeasure W := by
    rw [map_potentialMeasure_matrix_with_jacobian hS]
    congr 1
    funext q
    have hi : matrixAction B (e.symm q) = q := by
      rw [← affineMatrixEquiv_zero_apply B hne, e.apply_symm_apply]
    change W (matrixAction B (e.symm q)) - Real.log |B.det| + Real.log |B.det| = W q
    rw [hi, sub_add_cancel]
  rw [← hm, Measure.map_map e.symm.continuous.measurable e.continuous.measurable]
  have hid : e.symm ∘ e = (id : Space n → Space n) := by funext x; simp
  rw [hid, Measure.map_id]

/-- General symmetric whitening includes opposite logarithmic Jacobians in
the source and target. It need not preserve determinant one. -/
theorem weighted_moment_transport_general_symmetric_matrix
    {u W V : Space n → ℝ} (hu : Differentiable ℝ u) (hW : Measurable W) (hV : Measurable V)
    {K : Set (Space n)}
    (hpush : (potentialMeasure W).map (gradient u) = (potentialMeasure V).restrict K)
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsSymm) (hne : B.det ≠ 0) :
    let e := affineMatrixEquiv B 0 hne
    (potentialMeasure (fun y => W (matrixAction B y) - Real.log |B.det|)).map
      (gradient (u ∘ matrixAction B)) =
      (potentialMeasure (fun q => V (e.symm q) + Real.log |B.det|)).restrict (e '' K) := by
  dsimp only
  let e := affineMatrixEquiv B 0 hne
  rw [← map_potentialMeasure_inverse_matrix_with_jacobian hW B hne,
    Measure.map_map (measurable_gradient _) e.symm.continuous.measurable,
    gradient_symmetric_linear_conjugacy hu hB hne,
    ← Measure.map_map e.continuous.measurable (measurable_gradient _), hpush,
    map_restrict_affineMatrixEquiv, map_potentialMeasure_matrix_with_jacobian hV]

lemma weighted_density_general_symmetric_matrix
    {u W V : Space n → ℝ} (hu : Differentiable ℝ u)
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsSymm) (hne : B.det ≠ 0) (y : Space n) :
    Real.exp (-(W (matrixAction B y) - Real.log |B.det|) +
      (V ((affineMatrixEquiv B 0 hne).symm (gradient (u ∘ matrixAction B) y)) +
        Real.log |B.det|)) =
      |B.det| ^ 2 * Real.exp (-W (matrixAction B y) + V (gradient u (matrixAction B y))) := by
  have hD : 0 < |B.det| := abs_pos.mpr hne
  rw [gradient_comp_matrixAction hu, hB.eq]
  have he : (affineMatrixEquiv B 0 hne).symm (matrixAction B (gradient u (matrixAction B y))) =
      gradient u (matrixAction B y) := by
    rw [← affineMatrixEquiv_zero_apply B hne, (affineMatrixEquiv B 0 hne).symm_apply_apply]
  rw [he]
  have hexponent : -(W (matrixAction B y) - Real.log |B.det|) +
      (V (gradient u (matrixAction B y)) + Real.log |B.det|) =
      (-W (matrixAction B y) + V (gradient u (matrixAction B y))) +
        Real.log |B.det| + Real.log |B.det| := by ring
  rw [hexponent, Real.exp_add, Real.exp_add, Real.exp_log hD]
  ring

lemma abs_det_inverseSqrtMatrix_sq {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) :
    |(inverseSqrtMatrix A).det| ^ 2 = 1 / A.det := by
  have hh := congrArg Matrix.det (inverseSqrtMatrix_mul_self_mul_transpose hA)
  simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hh
  apply (eq_div_iff hA.det_pos.ne').mpr
  calc
    _ = (inverseSqrtMatrix A).det * A.det * (inverseSqrtMatrix A).det := by rw [sq_abs]; ring
    _ = 1 := hh

end KLS
end

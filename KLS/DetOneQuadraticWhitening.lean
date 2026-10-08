import KLS.SymmetricLinearMomentTransport

open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff NNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

lemma abs_det_inverseSqrtMatrix_of_det_one
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (hdet : A.det = 1) :
    |(inverseSqrtMatrix A).det| = 1 := by
  have hh := congrArg Matrix.det (inverseSqrtMatrix_mul_self_mul_transpose hA)
  simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one, hdet, mul_one] at hh
  have hsq := sq_abs ((inverseSqrtMatrix A).det)
  nlinarith [abs_nonneg ((inverseSqrtMatrix A).det)]

/-- The genuine inverse positive square root whitens the actual quadratic
polynomial. Symmetry and determinant normalization are derived from A. -/
lemma centeredQuadratic_inverseSqrtMatrix
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (y : Space n) :
    centeredQuadratic A 0 0 0 (matrixAction (inverseSqrtMatrix A) y) =
      centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 0 y := by
  let B := inverseSqrtMatrix A
  have hB : B.IsSymm := inverseSqrtMatrix_isSymm A
  have hwhite : B.transpose * A * B = 1 := by
    have hh := inverseSqrtMatrix_mul_self_mul_transpose hA
    change B * A * B.transpose = 1 at hh
    rw [hB.eq] at hh ⊢
    exact hh
  simp only [centeredQuadratic, sub_zero, inner_zero_left, zero_add]
  rw [inner_matrixAction_transpose, ← MomentMap.matrixAction_mul_apply,
    ← MomentMap.matrixAction_mul_apply, hwhite]

/-- A symmetric linear whitening preserves the temperature coefficient and
transforms only the affine source slope. -/
lemma affine_weight_comp_symmetric_matrix (u : Space n → ℝ) (s c : ℝ) (b : Space n)
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsSymm) :
    (fun x => s * u x + inner ℝ b x + c) ∘ matrixAction B =
      fun y => s * (u ∘ matrixAction B) y + inner ℝ (matrixAction B b) y + c := by
  funext y
  simp only [Function.comp_apply]
  rw [inner_matrixAction_transpose, hB.eq]

/-- The same actual inverse square root preserves the weighted weak moment
transport and exactly normalizes the determinant-one quadratic. -/
theorem weighted_moment_transport_inverseSqrtMatrix
    {u W V : Space n → ℝ} (hu : Differentiable ℝ u) (hW : Measurable W) (hV : Measurable V)
    {K : Set (Space n)}
    (hpush : (potentialMeasure W).map (gradient u) = (potentialMeasure V).restrict K)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (hdet : A.det = 1) :
    let B := inverseSqrtMatrix A
    let e := affineMatrixEquiv B 0 (by
      have hh := abs_det_inverseSqrtMatrix_of_det_one hA hdet
      intro hzero
      change (inverseSqrtMatrix A).det = 0 at hzero
      simp [hzero] at hh)
    (potentialMeasure (W ∘ matrixAction B)).map (gradient (u ∘ matrixAction B)) =
      (potentialMeasure (V ∘ e.symm)).restrict (e '' K) :=
  weighted_moment_transport_symmetric_matrix hu hW hV hpush
    (inverseSqrtMatrix_isSymm A) (abs_det_inverseSqrtMatrix_of_det_one hA hdet)

lemma weighted_density_symmetric_matrix
    {u W V : Space n → ℝ} (hu : Differentiable ℝ u)
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsSymm) (hne : B.det ≠ 0) (y : Space n) :
    Real.exp (-(W ∘ matrixAction B) y + (V ∘ (affineMatrixEquiv B 0 hne).symm)
      (gradient (u ∘ matrixAction B) y)) =
      Real.exp (-W (matrixAction B y) + V (gradient u (matrixAction B y))) := by
  rw [gradient_comp_matrixAction hu, hB.eq]
  have he : (affineMatrixEquiv B 0 hne).symm (matrixAction B (gradient u (matrixAction B y))) =
      gradient u (matrixAction B y) := by
    rw [← affineMatrixEquiv_zero_apply B hne, (affineMatrixEquiv B 0 hne).symm_apply_apply]
  simp only [Function.comp_apply, he]

lemma flatness_under_inverseSqrtMatrix
    {u : Space n → ℝ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    {S : Set (Space n)} {η : ℝ}
    (hbound : ∀ x ∈ S, |u x - centeredQuadratic A 0 0 0 x| ≤ η)
    {y : Space n} (hy : matrixAction (inverseSqrtMatrix A) y ∈ S) :
    |(u ∘ matrixAction (inverseSqrtMatrix A)) y -
      centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 0 y| ≤ η := by
  rw [← centeredQuadratic_inverseSqrtMatrix hA]
  exact hbound _ hy

end KLS
end

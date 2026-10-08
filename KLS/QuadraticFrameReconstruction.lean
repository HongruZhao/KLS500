import KLS.IterationAffineCoefficients

open Matrix Set Filter Metric InnerProductSpace
open scoped Topology BigOperators Matrix.Norms.Elementwise
noncomputable section
namespace KLS
variable {n : ℕ}

lemma centeredQuadratic_add_coefficients
    (A B : Matrix (Fin n) (Fin n) ℝ) (p q : Space n) (a b : ℝ) (x : Space n) :
    centeredQuadratic (A + B) 0 (p + q) (a + b) x =
      centeredQuadratic A 0 p a x + centeredQuadratic B 0 q b x := by
  simp only [centeredQuadratic, sub_zero, matrixAction_add_matrices, inner_add_left, inner_add_right]
  ring

lemma centeredQuadratic_sub_coefficients
    (A B : Matrix (Fin n) (Fin n) ℝ) (p q : Space n) (a b : ℝ) (x : Space n) :
    centeredQuadratic (A - B) 0 (p - q) (a - b) x =
      centeredQuadratic A 0 p a x - centeredQuadratic B 0 q b x := by
  simp only [centeredQuadratic, sub_zero, matrixAction_sub_matrices, inner_sub_left, inner_sub_right]
  ring

lemma matrixAction_inverse_cancel {T : Matrix (Fin n) (Fin n) ℝ} (hT : T.det ≠ 0) (x : Space n) :
    matrixAction T⁻¹ (matrixAction T x) = x := by
  rw [← MomentMap.matrixAction_mul_apply, Matrix.nonsing_inv_mul T (isUnit_iff_ne_zero.mpr hT),
    matrixAction_one_apply]

/-- Pulling back a quadratic by a genuine frame and a scalar spatial change
transforms all three coefficients by the same explicit formulas. -/
lemma centeredQuadratic_frame_scaled
    {T : Matrix (Fin n) (Fin n) ℝ} (hT : T.det ≠ 0)
    (A : Matrix (Fin n) (Fin n) ℝ) (p : Space n) (a r : ℝ) (y : Space n) :
    centeredQuadratic (T⁻¹.transpose * A * T⁻¹) 0
      (r • matrixAction T⁻¹.transpose p) (r ^ 2 * a) (r • matrixAction T y) =
      r ^ 2 * centeredQuadratic A 0 p a y := by
  have hcancel := matrixAction_inverse_cancel hT y
  simp only [centeredQuadratic, sub_zero, map_smul, inner_smul_right, real_inner_smul_left,
    MomentMap.matrixAction_mul_apply]
  rw [hcancel, inner_matrixAction_transpose, Matrix.transpose_transpose, hcancel]
  rw [← inner_matrixAction_transpose, hcancel]
  ring

lemma iteration_frame_det_ne_zero
    {d₀ : NormalizedWeightedMomentData n 1 1} {ρ Q β : ℝ} {j : ℕ}
    (s : WeightedIterationState d₀ ρ Q β j) : s.frame.det ≠ 0 := by
  intro hzero
  have hh := s.determinant
  simp [hzero] at hh

end KLS
end

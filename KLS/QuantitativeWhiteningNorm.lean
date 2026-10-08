import KLS.RelativeMomentDensity
import KLS.HarmonicCorrectionCoefficientBounds

open Matrix Set Metric InnerProductSpace
open scoped Topology ContDiff BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

lemma quadratic_bounds_of_matrix_increment
    {A : Matrix (Fin n) (Fin n) ℝ} {η : ℝ}
    (hA : ‖matrixAction (A - 1)‖ ≤ η) (x : Space n) :
    (1 - η) * ‖x‖ ^ 2 ≤ inner ℝ x (matrixAction A x) ∧
      inner ℝ x (matrixAction A x) ≤ (1 + η) * ‖x‖ ^ 2 := by
  have he : matrixAction (A - 1) x = matrixAction A x - x := by
    rw [matrixAction_sub_matrices, matrixAction_one_apply]
  have hop : ‖matrixAction (A - 1) x‖ ≤ η * ‖x‖ :=
    ((matrixAction (A - 1)).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right hA (norm_nonneg x))
  have hi : |inner ℝ x (matrixAction A x) - ‖x‖ ^ 2| ≤ η * ‖x‖ ^ 2 := by
    calc
      _ = |inner ℝ x (matrixAction (A - 1) x)| := by
        rw [he, inner_sub_right, real_inner_self_eq_norm_sq]
      _ ≤ ‖x‖ * ‖matrixAction (A - 1) x‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖x‖ * (η * ‖x‖) := mul_le_mul_of_nonneg_left hop (norm_nonneg x)
      _ = _ := by ring
  have hh := abs_le.mp hi
  constructor <;> nlinarith

lemma inner_inverseSqrtMatrix_identity {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) (y : Space n) :
    inner ℝ (matrixAction (inverseSqrtMatrix A) y)
      (matrixAction A (matrixAction (inverseSqrtMatrix A) y)) = ‖y‖ ^ 2 := by
  have hh := centeredQuadratic_inverseSqrtMatrix hA y
  simp only [centeredQuadratic, sub_zero, inner_zero_left, zero_add, add_zero,
    matrixAction_one_apply, real_inner_self_eq_norm_sq] at hh
  linarith

lemma norm_le_one_add_twice_of_quadratic_lower
    {a b η : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hη : 0 ≤ η) (hηhalf : η ≤ 1 / 2)
    (hq : (1 - η) * a ^ 2 ≤ b ^ 2) : a ≤ (1 + 2 * η) * b := by
  have hd : 0 < 1 - η := by linarith
  have hc : 1 ≤ (1 - η) * (1 + 2 * η) := by nlinarith
  have ha2 : a ^ 2 ≤ (1 + 2 * η) * b ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right hc (sq_nonneg b)
    nlinarith
  have hs : (1 + 2 * η) * b ^ 2 ≤ ((1 + 2 * η) * b) ^ 2 := by nlinarith [sq_nonneg (η * b)]
  exact (sq_le_sq₀ ha (mul_nonneg (by linarith) hb)).mp (ha2.trans hs)

/-- The actual inverse square root expands lengths by at most 1+2 eta
when the approximating Hessian differs from the identity by eta <= 1/2. -/
theorem norm_inverseSqrtMatrix_action_le
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) {η : ℝ}
    (hη : 0 ≤ η) (hηhalf : η ≤ 1 / 2) (hclose : ‖matrixAction (A - 1)‖ ≤ η) :
    ‖matrixAction (inverseSqrtMatrix A)‖ ≤ 1 + 2 * η := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by linarith)
  intro y
  apply norm_le_one_add_twice_of_quadratic_lower (norm_nonneg _) (norm_nonneg _) hη hηhalf
  have hh := (quadratic_bounds_of_matrix_increment hclose (matrixAction (inverseSqrtMatrix A) y)).1
  rwa [inner_inverseSqrtMatrix_identity hA y] at hh

/-- The inverse coordinate change has the same useful linear-in-eta bound. -/
theorem norm_inverse_inverseSqrtMatrix_action_le
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) {η : ℝ}
    (hη : 0 ≤ η) (hclose : ‖matrixAction (A - 1)‖ ≤ η) :
    ‖matrixAction ((inverseSqrtMatrix A)⁻¹)‖ ≤ 1 + η := by
  let B := inverseSqrtMatrix A
  have hBdet : IsUnit B.det := isUnit_iff_ne_zero.mpr (inverseSqrtMatrix_det_ne_zero_of_posDef hA)
  have hcancel (y : Space n) : matrixAction B (matrixAction B⁻¹ y) = y := by
    rw [← MomentMap.matrixAction_mul_apply, Matrix.mul_nonsing_inv B hBdet, matrixAction_one_apply]
  apply ContinuousLinearMap.opNorm_le_bound _ (by linarith)
  intro y
  have he := inner_inverseSqrtMatrix_identity hA (matrixAction B⁻¹ y)
  change inner ℝ (matrixAction B (matrixAction B⁻¹ y))
    (matrixAction A (matrixAction B (matrixAction B⁻¹ y))) = ‖matrixAction B⁻¹ y‖ ^ 2 at he
  rw [hcancel] at he
  have hh := (quadratic_bounds_of_matrix_increment hclose y).2
  rw [he] at hh
  have hs : (1 + η) * ‖y‖ ^ 2 ≤ ((1 + η) * ‖y‖) ^ 2 := by nlinarith [sq_nonneg (η * ‖y‖)]
  have hp : 0 ≤ (1 + η) * ‖y‖ := mul_nonneg (by linarith) (norm_nonneg y)
  nlinarith [norm_nonneg (matrixAction B⁻¹ y)]

end KLS
end

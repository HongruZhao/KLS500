import KLS.IterationQuadraticApproximation

open Matrix Set Filter Metric InnerProductSpace
open scoped Topology BigOperators Matrix.Norms.Elementwise
noncomputable section
namespace KLS
variable {n : ℕ}

lemma centeredQuadratic_coefficient_difference_le
    (A B : Matrix (Fin n) (Fin n) ℝ) (p q : Space n) (a b : ℝ) (x : Space n) :
    |centeredQuadratic A 0 p a x - centeredQuadratic B 0 q b x| ≤
      |a - b| + ‖p - q‖ * ‖x‖ + (1 / 2 : ℝ) * ‖matrixAction (A - B)‖ * ‖x‖ ^ 2 := by
  rw [← centeredQuadratic_sub_coefficients]
  simp only [centeredQuadratic, sub_zero]
  have hinner := abs_real_inner_le_norm x (matrixAction (A - B) x)
  have hop := (matrixAction (A - B)).le_opNorm x
  have hq : |(1 / 2 : ℝ) * inner ℝ x (matrixAction (A - B) x)| ≤
      (1 / 2 : ℝ) * ‖matrixAction (A - B)‖ * ‖x‖ ^ 2 := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    calc
      _ ≤ (1 / 2 : ℝ) * (‖x‖ * ‖matrixAction (A - B) x‖) := mul_le_mul_of_nonneg_left hinner (by norm_num)
      _ ≤ (1 / 2 : ℝ) * (‖x‖ * (‖matrixAction (A - B)‖ * ‖x‖)) := by gcongr
      _ = _ := by ring
  calc
    _ ≤ |a - b| + |inner ℝ (p - q) x| + |(1 / 2 : ℝ) * inner ℝ x (matrixAction (A - B) x)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ _ := add_le_add (add_le_add le_rfl (abs_real_inner_le_norm _ _)) hq

lemma quadratic_error_of_coefficient_bounds
    {u : Space n → ℝ} {A H : Matrix (Fin n) (Fin n) ℝ}
    {p q : Space n} {a b e t K : ℝ} {x : Space n}
    (he : 0 ≤ e) (ht : 0 ≤ t) (hK : 0 ≤ K) (hx : ‖x‖ ≤ t)
    (hu : |u x - centeredQuadratic A 0 p a x| ≤ e * t ^ 2)
    (hH : ‖matrixAction (A - H)‖ ≤ 4 * K * e)
    (hp : ‖p - q‖ ≤ 2 * K * e * t)
    (ha : |a - b| ≤ K * e * t ^ 2) :
    |u x - centeredQuadratic H 0 q b x| ≤ (1 + 5 * K) * e * t ^ 2 := by
  have hq := centeredQuadratic_coefficient_difference_le A H p q a b x
  have hcoef : |centeredQuadratic A 0 p a x - centeredQuadratic H 0 q b x| ≤
      5 * K * e * t ^ 2 := by
    calc
      _ ≤ |a - b| + ‖p - q‖ * ‖x‖ + (1 / 2 : ℝ) * ‖matrixAction (A - H)‖ * ‖x‖ ^ 2 := hq
      _ ≤ K * e * t ^ 2 + (2 * K * e * t) * t + (1 / 2 : ℝ) * (4 * K * e) * t ^ 2 := by
        gcongr
      _ = _ := by ring
  calc
    _ ≤ |u x - centeredQuadratic A 0 p a x| +
        |centeredQuadratic A 0 p a x - centeredQuadratic H 0 q b x| := abs_sub_le _ _ _
    _ ≤ e * t ^ 2 + 5 * K * e * t ^ 2 := add_le_add hu hcoef
    _ = _ := by ring

end KLS
end

import KLS.WeightedPointwiseHessian

open Matrix Set Filter Metric InnerProductSpace Asymptotics
open scoped Topology BigOperators Matrix.Norms.Elementwise
noncomputable section
namespace KLS
variable {n : ℕ}

/-- A central difference formed directly from values of the actual function. -/
def quadraticCentralDifference (u : Space n → ℝ) (h : ℝ) (v c : Space n) : ℝ :=
  (u (c + h • v) + u (c - h • v) - 2 * u c) / h ^ 2

lemma continuous_quadraticCentralDifference {u : Space n → ℝ} (hu : Continuous u)
    (h : ℝ) (v : Space n) : Continuous (quadraticCentralDifference u h v) := by
  unfold quadraticCentralDifference
  fun_prop

/-- A scalar quadratic approximation bounds the error of a genuine central
difference. The linear coefficient cancels exactly. -/
lemma quadraticCentralDifference_error_le
    {u : Space n → ℝ} {H : Matrix (Fin n) (Fin n) ℝ}
    {p c v : Space n} {h E : ℝ} (hh : h ≠ 0)
    (hp : |u (c + h • v) - centeredQuadratic H c p (u c) (c + h • v)| ≤ E)
    (hm : |u (c - h • v) - centeredQuadratic H c p (u c) (c - h • v)| ≤ E) :
    |quadraticCentralDifference u h v c - inner ℝ v (matrixAction H v)| ≤ 2 * E / h ^ 2 := by
  have hq := centeredQuadratic_central_sum H c p (u c) (h • v)
  simp only [map_smul, real_inner_smul_left, inner_smul_right] at hq
  have heq : quadraticCentralDifference u h v c - inner ℝ v (matrixAction H v) =
      ((u (c + h • v) - centeredQuadratic H c p (u c) (c + h • v)) +
        (u (c - h • v) - centeredQuadratic H c p (u c) (c - h • v))) / h ^ 2 := by
    unfold quadraticCentralDifference
    field_simp
    nlinarith
  rw [heq, abs_div, abs_of_pos (sq_pos_of_ne_zero hh)]
  apply div_le_div_of_nonneg_right _ (sq_nonneg h)
  exact (abs_add_le _ _).trans (by linarith)

/-- Uniform geometric Taylor estimates give a uniformly vanishing central
difference error for every direction of norm at most two. -/
theorem geometric_quadraticCentralDifference_error
    {u : Space n → ℝ} {H : Space n → Matrix (Fin n) (Fin n) ℝ}
    {p : Space n → Space n} {S : Set (Space n)} {D r β : ℝ}
    (hr : 0 < r)
    (hb : ∀ c ∈ S, ∀ (j : ℕ) (y : Space n), ‖y - c‖ ≤ r ^ j / 2 →
      |u y - centeredQuadratic (H c) c (p c) (u c) y| ≤ D * β ^ j * r ^ (2 * j))
    (j : ℕ) {c v : Space n} (hc : c ∈ S) (hv : ‖v‖ ≤ 2) :
    |quadraticCentralDifference u (r ^ j / 4) v c - inner ℝ v (matrixAction (H c) v)| ≤
      32 * D * β ^ j := by
  have hh : 0 < r ^ j / 4 := by positivity
  have hp : ‖(c + (r ^ j / 4) • v) - c‖ ≤ r ^ j / 2 := by
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hh]
    nlinarith
  have hm : ‖(c - (r ^ j / 4) • v) - c‖ ≤ r ^ j / 2 := by
    rw [show c - (r ^ j / 4) • v - c = -((r ^ j / 4) • v) by abel, norm_neg]
    simpa only [add_sub_cancel_left] using hp
  have he := quadraticCentralDifference_error_le hh.ne' (hb c hc j _ hp) (hb c hc j _ hm)
  apply he.trans_eq
  rw [show r ^ (2 * j) = (r ^ j) ^ 2 by rw [← pow_mul, Nat.mul_comm]]
  field_simp
  ring

end KLS
end

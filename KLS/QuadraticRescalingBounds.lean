import KLS.MomentTemperatureRescaling

open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff NNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

lemma centeredQuadratic_scalar_rescaling (A : Matrix (Fin n) (Fin n) ℝ)
    (x₀ p : Space n) (a r : ℝ) (y : Space n) :
    centeredQuadratic A x₀ p a (x₀ + r • y) =
      a + r * inner ℝ p y + r ^ 2 * centeredQuadratic A 0 0 0 y := by
  simp only [centeredQuadratic, add_sub_cancel_left, sub_zero, inner_zero_left, zero_add,
    map_smul, inner_smul_right, real_inner_smul_left]
  ring

lemma quadratic_rescaling_error_identity (u : Space n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (x₀ p : Space n) (a : ℝ) {r : ℝ} (hr : r ≠ 0) (y : Space n) :
    quadraticallyRescaledPotential u x₀ p a r y - centeredQuadratic A 0 0 0 y =
      (u (x₀ + r • y) - centeredQuadratic A x₀ p a (x₀ + r • y)) / r ^ 2 := by
  rw [centeredQuadratic_scalar_rescaling]
  unfold quadraticallyRescaledPotential
  field_simp
  ring

lemma scalar_rescaling_mem_closedBall (x₀ : Space n) {r T : ℝ} (hr : 0 ≤ r)
    {y : Space n} (hy : y ∈ closedBall (0 : Space n) T) :
    x₀ + r • y ∈ closedBall x₀ (r * T) := by
  rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
  exact mul_le_mul_of_nonneg_left (show ‖y‖ ≤ T by simpa only [mem_closedBall, dist_zero_right] using hy) hr

/-- The actual quadratic error scales with r squared under normalization. -/
theorem quadratic_rescaling_flatness_bound (u : Space n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (x₀ p : Space n) (a : ℝ) {r T ε : ℝ} (hr : 0 < r)
    (hbound : ∀ x ∈ closedBall x₀ (r * T), |u x - centeredQuadratic A x₀ p a x| ≤ ε * r ^ 2)
    {y : Space n} (hy : y ∈ closedBall (0 : Space n) T) :
    |quadraticallyRescaledPotential u x₀ p a r y - centeredQuadratic A 0 0 0 y| ≤ ε := by
  rw [quadratic_rescaling_error_identity u A x₀ p a hr.ne', abs_div, abs_of_pos (sq_pos_of_pos hr)]
  exact (div_le_iff₀ (sq_pos_of_pos hr)).mpr (hbound _ (scalar_rescaling_mem_closedBall x₀ hr.le hy))

/-- The actual density error is preserved by quadratic normalization, with
the explicit transformed source potential rather than an assumed unit weight. -/
theorem quadratic_rescaling_density_bound {u V : Space n → ℝ} (hu : Differentiable ℝ u)
    (x₀ p : Space n) (a : ℝ) {r T ε : ℝ} (hr : 0 < r)
    (hdensity : ∀ x ∈ closedBall x₀ (r * T), |Real.exp (-u x + V (gradient u x)) - 1| ≤ ε ^ 2)
    {y : Space n} (hy : y ∈ closedBall (0 : Space n) T) :
    |Real.exp (-scalarNormalizedPotential u x₀ r y + scalarNormalizedPotential V p r
      (gradient (quadraticallyRescaledPotential u x₀ p a r) y)) - 1| ≤ ε ^ 2 := by
  rw [quadratic_rescaling_density_identity hu x₀ p a hr.ne']
  exact hdensity _ (scalar_rescaling_mem_closedBall x₀ hr.le hy)

end KLS
end

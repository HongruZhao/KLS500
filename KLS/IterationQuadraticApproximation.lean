import KLS.IterationPotentialReconstruction

open Matrix Set Filter Metric InnerProductSpace
open scoped Topology BigOperators Matrix.Norms.Elementwise
noncomputable section
namespace KLS
variable {n : ℕ}

lemma matrixAction_cancel_inverse {T : Matrix (Fin n) (Fin n) ℝ} (hT : T.det ≠ 0) (x : Space n) :
    matrixAction T (matrixAction T⁻¹ x) = x := by
  rw [← MomentMap.matrixAction_mul_apply, Matrix.mul_nonsing_inv T (isUnit_iff_ne_zero.mpr hT),
    matrixAction_one_apply]

lemma normalized_weighted_quadratic_bound (d : NormalizedWeightedMomentData n 1 1)
    {y : Space n} (hy : y ∈ closedBall (0 : Space n) 1) :
    |d.u y - centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 d.c y| ≤ d.epsilon := by
  have hb := d.bound y hy
  change |(d.u y - centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 d.c y) / d.epsilon| ≤ 1 at hb
  rw [abs_div, abs_of_pos d.epsilon_pos] at hb
  simpa only [one_mul] using (div_le_iff₀ d.epsilon_pos).mp hb

/-- Every normalized error bound gives the exact finite quadratic
approximation on the corresponding ellipsoid in the original coordinates. -/
theorem iteration_quadratic_error_on_ellipsoid
    {d₀ : NormalizedWeightedMomentData n 1 1} {ρ Q β : ℝ}
    (s : (j : ℕ) → WeightedIterationState d₀ ρ Q β j)
    (links : ∀ j, WeightedIterationLink (s j) (s (j + 1)))
    (hstart : s 0 = initialWeightedIterationState d₀ ρ Q β) (hρ : 0 < ρ)
    (j : ℕ) {y : Space n} (hy : y ∈ closedBall (0 : Space n) 1) :
    |d₀.u ((ρ / 2) ^ j • matrixAction (s j).frame y) -
        centeredQuadratic (frameHessian (s j).frame) 0
          (iterationSlope s links j) (iterationConstant s links j)
          ((ρ / 2) ^ j • matrixAction (s j).frame y)| ≤
      d₀.epsilon * β ^ j * (ρ / 2) ^ (2 * j) := by
  rw [iteration_quadratic_error_identity s links hstart hρ.ne', abs_mul,
    abs_of_nonneg (pow_nonneg (by positivity) _)]
  have hb := mul_le_mul_of_nonneg_left (normalized_weighted_quadratic_bound (s j).data hy)
    (pow_nonneg (by positivity : 0 ≤ ρ / 2) (2 * j))
  rw [(s j).epsilon_eq] at hb
  exact hb.trans_eq (by ring)

lemma norm_normalized_frame_point_le_one
    {T : Matrix (Fin n) (Fin n) ℝ} {r : ℝ} (hr : 0 < r)
    (hinv : ‖matrixAction T⁻¹‖ ≤ 2) {x : Space n} (hx : ‖x‖ ≤ r / 2) :
    ‖r⁻¹ • matrixAction T⁻¹ x‖ ≤ 1 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
  have hb := (matrixAction T⁻¹).le_opNorm x
  have hm : ‖matrixAction T⁻¹ x‖ ≤ r := by
    calc
      _ ≤ ‖matrixAction T⁻¹‖ * ‖x‖ := hb
      _ ≤ 2 * (r / 2) := mul_le_mul hinv hx (norm_nonneg _) (by norm_num)
      _ = r := by ring
  calc
    _ ≤ r⁻¹ * r := mul_le_mul_of_nonneg_left hm (inv_nonneg.mpr hr.le)
    _ = 1 := inv_mul_cancel₀ hr.ne'

/-- Actual quadratic approximation of the original function on ordinary
shrinking balls, obtained from the proved inverse-frame bounds. -/
theorem iteration_quadratic_error_on_ball
    {d₀ : NormalizedWeightedMomentData n 1 1} {ρ Q β : ℝ}
    (s : (j : ℕ) → WeightedIterationState d₀ ρ Q β j)
    (links : ∀ j, WeightedIterationLink (s j) (s (j + 1)))
    (hstart : s 0 = initialWeightedIterationState d₀ ρ Q β) (hρ : 0 < ρ)
    (hinv : ∀ j, ‖matrixAction (s j).frame⁻¹‖ ≤ 2)
    (j : ℕ) {x : Space n} (hx : ‖x‖ ≤ (ρ / 2) ^ j / 2) :
    |d₀.u x - centeredQuadratic (frameHessian (s j).frame) 0
        (iterationSlope s links j) (iterationConstant s links j) x| ≤
      d₀.epsilon * β ^ j * (ρ / 2) ^ (2 * j) := by
  let y : Space n := ((ρ / 2) ^ j)⁻¹ • matrixAction (s j).frame⁻¹ x
  have hr : 0 < (ρ / 2) ^ j := pow_pos (by positivity) j
  have hy : y ∈ closedBall (0 : Space n) 1 := by
    rw [mem_closedBall_zero_iff]
    exact norm_normalized_frame_point_le_one hr (hinv j) hx
  have hpoint : (ρ / 2) ^ j • matrixAction (s j).frame y = x := by
    simp only [y, map_smul, smul_smul]
    rw [matrixAction_cancel_inverse (iteration_frame_det_ne_zero (s j)), mul_inv_cancel₀ hr.ne', one_smul]
  simpa only [hpoint] using iteration_quadratic_error_on_ellipsoid s links hstart hρ j hy

end KLS
end

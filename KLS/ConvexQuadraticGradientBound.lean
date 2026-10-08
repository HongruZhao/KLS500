import KLS.QuadraticPeanoJet

open Matrix Set Filter Metric InnerProductSpace Asymptotics
open scoped Topology BigOperators Matrix.Norms.Elementwise
noncomputable section
namespace KLS
variable {n : ℕ}

/-- Convex supporting planes turn a genuine scalar quadratic approximation
into a quantitative estimate for the actual gradient at a nonzero point. -/
theorem norm_gradient_sub_quadratic_le
    {u : Space n → ℝ} (huc : ConvexOn ℝ univ u)
    {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsSymm)
    {p : Space n} {a η t : ℝ} {x : Space n}
    (hud : DifferentiableAt ℝ u x) (hx : x ≠ 0)
    (hη : 0 ≤ η) (ht : 0 < t) (htone : t ≤ 1)
    (hb : ∀ y : Space n, ‖y‖ ≤ 2 * ‖x‖ →
      |u y - centeredQuadratic H 0 p a y| ≤ η * ‖y‖ ^ 2) :
    ‖gradient u x - (p + matrixAction H x)‖ ≤
      (5 * η / t + t / 2 * ‖matrixAction H‖) * ‖x‖ := by
  let d := gradient u x - (p + matrixAction H x)
  change ‖d‖ ≤ _
  by_cases hd : d = 0
  · rw [hd, norm_zero]
    positivity
  have hdpos : 0 < ‖d‖ := norm_pos_iff.mpr hd
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let v : Space n := ‖d‖⁻¹ • d
  have hv : ‖v‖ = 1 := by
    simp only [v, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hdpos), inv_mul_cancel₀ hdpos.ne']
  let z : Space n := (t * ‖x‖) • v
  have hz : ‖z‖ = t * ‖x‖ := by
    simp only [z, norm_smul, Real.norm_eq_abs, abs_of_pos (mul_pos ht hxpos), hv, mul_one]
  let y := x + z
  have hy : ‖y‖ ≤ 2 * ‖x‖ := by
    calc
      _ ≤ ‖x‖ + ‖z‖ := norm_add_le _ _
      _ = ‖x‖ + t * ‖x‖ := by rw [hz]
      _ ≤ _ := by nlinarith
  have hyx : y - x = z := by dsimp [y]; abel
  have hsupport := gradient_mem_convexSubgradient huc hud y
  change u x + inner ℝ (gradient u x) (y - x) ≤ u y at hsupport
  have hquadratic := centeredQuadratic_support_identity hH 0 p a x y
  rw [hyx] at hsupport hquadratic
  simp only [sub_zero] at hquadratic
  have hquad := quadratic_part_le_opNorm_radius_sq H 0 (norm_nonneg z)
    (x := z) (by simpa only [mem_closedBall_zero_iff] using le_refl ‖z‖)
  simp only [sub_zero] at hquad
  rw [hz] at hquad
  have hinner : inner ℝ d z = t * ‖x‖ * ‖d‖ := by
    simp only [z, v, inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  have hdinner : inner ℝ d z = inner ℝ (gradient u x) z - inner ℝ (p + matrixAction H x) z := by
    simp only [d, inner_sub_left]
  have hbx := hb x (by linarith [norm_nonneg x])
  have hby := hb y hy
  have hy2 : ‖y‖ ^ 2 ≤ 4 * ‖x‖ ^ 2 := by nlinarith [norm_nonneg y]
  have hyη := mul_le_mul_of_nonneg_left hy2 hη
  have hbound : t * ‖x‖ * ‖d‖ ≤
      (5 * η + (1 / 2 : ℝ) * ‖matrixAction H‖ * t ^ 2) * ‖x‖ ^ 2 := by
    have hbxlow := (abs_le.mp hbx).1
    have hbyhigh := (abs_le.mp hby).2
    nlinarith
  apply (mul_le_mul_iff_right₀ (mul_pos ht hxpos)).mp
  calc
    _ ≤ (5 * η + (1 / 2 : ℝ) * ‖matrixAction H‖ * t ^ 2) * ‖x‖ ^ 2 := hbound
    _ = _ := by field_simp

end KLS
end

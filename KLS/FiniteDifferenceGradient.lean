import KLS.MomentMapFiniteDifference

open Set InnerProductSpace
open scoped NNReal
noncomputable section
namespace KLS
variable {n : ℕ}

/-- Supporting planes turn an actual second-difference bound into a quadratic
upper bound. The function is only convex and differentiable. -/
theorem convex_quadratic_upper_of_secondDifference
    {u : Space n → ℝ} {C : ℝ≥0} (hc : ConvexOn ℝ univ u)
    (hd : Differentiable ℝ u)
    (hbound : ∀ h x, symmetricSecondDifference u h x ≤ (C : ℝ) * ‖h‖ ^ 2)
    (x h : Space n) :
    u (x + h) ≤ u x + inner ℝ (gradient u x) h + (C : ℝ) * ‖h‖ ^ 2 := by
  have hm := convex_supporting_fderiv hc hd x (x - h)
  rw [show x - h - x = -h by abel, map_neg, ← inner_gradient_left] at hm
  have hh := hbound h x
  unfold symmetricSecondDifference at hh
  linarith

/-- A conservative gradient bound derived from finite differences alone.
The coefficient4 is not asserted sharp. No source Hessian is assumed. -/
theorem norm_gradient_sub_le_of_secondDifference
    {u : Space n → ℝ} {C : ℝ≥0} (hc : ConvexOn ℝ univ u)
    (hd : Differentiable ℝ u)
    (hbound : ∀ h x, symmetricSecondDifference u h x ≤ (C : ℝ) * ‖h‖ ^ 2)
    (x y : Space n) :
    ‖gradient u y - gradient u x‖ ≤ 4 * (C : ℝ) * ‖y - x‖ := by
  by_cases hxy : y = x
  · subst y
    simp
  have hr : 0 < ‖y - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  let p := gradient u y - gradient u x
  change ‖p‖ ≤ _
  by_cases hp : p = 0
  · rw [hp, norm_zero]
    positivity
  have hp0 : 0 < ‖p‖ := norm_pos_iff.mpr hp
  let h : Space n := (‖y - x‖ / ‖p‖) • p
  have hnorm : ‖h‖ = ‖y - x‖ := by
    dsimp [h]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hr hp0)]
    field_simp
  have hinner : inner ℝ p h = ‖y - x‖ * ‖p‖ := by
    dsimp [h]
    rw [inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  have hu := convex_quadratic_upper_of_secondDifference hc hd hbound x (y - x + h)
  rw [show x + (y - x + h) = y + h by abel, inner_add_right] at hu
  have hy := convex_supporting_fderiv hc hd y (y + h)
  rw [show y + h - y = h by abel, ← inner_gradient_left] at hy
  have hx := convex_supporting_fderiv hc hd x y
  rw [← inner_gradient_left] at hx
  have hi : inner ℝ p h ≤ (C : ℝ) * ‖y - x + h‖ ^ 2 := by
    dsimp [p]
    rw [inner_sub_left]
    linarith
  have hnormsum : ‖y - x + h‖ ≤ 2 * ‖y - x‖ := by
    have hh := norm_add_le (y - x) h
    rw [hnorm] at hh
    linarith
  have hsquare : ‖y - x + h‖ ^ 2 ≤ 4 * ‖y - x‖ ^ 2 := by
    nlinarith [norm_nonneg (y - x + h)]
  have hquad := mul_le_mul_of_nonneg_left hsquare C.coe_nonneg
  rw [hinner] at hi
  have hf : ‖y - x‖ * ‖p‖ ≤ 4 * (C : ℝ) * ‖y - x‖ ^ 2 := by
    nlinarith
  apply (mul_le_mul_iff_right₀ hr).mp
  convert hf using 1
  ring

/-- The literal gradient is globally Lipschitz under the proved finite-
difference criterion; differentiability replaces any Hessian premise. -/
theorem lipschitzWith_gradient_of_secondDifference
    {u : Space n → ℝ} {C : ℝ≥0} (hc : ConvexOn ℝ univ u)
    (hd : Differentiable ℝ u)
    (hbound : ∀ h x, symmetricSecondDifference u h x ≤ (C : ℝ) * ‖h‖ ^ 2) :
    LipschitzWith (4 * C) (gradient u) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_eq_norm, NNReal.coe_mul, NNReal.coe_ofNat] using
    norm_gradient_sub_le_of_secondDifference hc hd hbound y x

end KLS
end

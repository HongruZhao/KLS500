import KLS.NormalizedSectionInterior

/-! An explicit engulfing inequality at every relatively deep point of an
actual bounded section. This estimates the original support-plane deficit,
so it is invariant under the affine normalization used in the proof. -/

open MeasureTheory InnerProductSpace Set Filter Metric
open scoped Topology NNReal ENNReal

noncomputable section
namespace KLS

variable {n : ℕ}

def sectionEngulfingConstant (n : ℕ) (a b : ℝ≥0∞) (θ : ℝ) : ℝ :=
  1 + 4 * ((n : ℝ) + 1) ^ 3 / normalizedSectionWidthConstant n a b θ

theorem sectionEngulfingConstant_pos (hn : 0 < n) {a b : ℝ≥0∞}
    (ha : 0 < a) (hatop : a < ∞) (hb : 0 < b) (hbtop : b < ∞)
    {θ : ℝ} (hθ : 0 < θ) : 0 < sectionEngulfingConstant n a b θ := by
  have hη := normalizedSectionWidthConstant_pos hn ha hatop hb hbtop hθ
  unfold sectionEngulfingConstant
  positivity

/-- Every point in the section has bounded deficit above every support plane
at a point with fixed relative depth. No differentiability is required. -/
theorem support_deficit_le_sectionEngulfingConstant
    (hn : 0 < n) {a b : ℝ≥0∞}
    (ha : 0 < a) (hatop : a < ∞) (hb : 0 < b) (hbtop : b < ∞)
    {θ : ℝ} (hθ : 0 < θ) {u : Space n → ℝ} {K : Set (Space n)}
    (hK : IsCompact K) (hc : Convex ℝ K) (hne : (interior K).Nonempty)
    (hucont : Continuous u) (huconvex : ConvexOn ℝ univ u)
    (hboundary : ∀ z ∈ frontier K, 0 ≤ u z)
    {h : ℝ} (hh : 0 < h) (hosc : ∀ z ∈ K, -h ≤ u z ∧ u z ≤ 0)
    (hlower : ∀ S : Set (Space n), IsCompact S → S ⊆ K →
      a * volume S ≤ volume (convexSubgradientImage u S))
    (hupper : ∀ S : Set (Space n), IsOpen S → S ⊆ K →
      volume (convexSubgradientImage u S) ≤ b * volume S)
    {x y p : Space n} (hx : x ∈ K) (hy : y ∈ K) (hdepth : θ * h ≤ -u x)
    (hp : p ∈ convexSubgradient u x) :
    u y - u x - inner ℝ p (y - x) ≤ sectionEngulfingConstant n a b θ * h := by
  obtain ⟨e, _, heouter, hedeep⟩ :=
    exists_normalization_with_deep_interior_ball_and_slope_bound hn ha hatop hb hbtop hθ
      hK hc hne hucont huconvex hboundary hh hosc hlower hupper
  let q : Space n := e.symm.linear.toLinearMap.adjoint p
  have hq : q ∈ convexSubgradient (fun z => u (e.symm z)) (e x) := by
    have hh := (mem_convexSubgradient_affine_iff e.symm.linear (e.symm 0) (e x) p).mpr
      (show p ∈ convexSubgradient u (e.symm.linear (e x) + e.symm 0) from by
        simpa only [← continuousAffineEquiv_apply_eq_linear_add e.symm, e.symm_apply_apply] using hp)
    simpa only [← continuousAffineEquiv_apply_eq_linear_add e.symm] using hh
  have hqnorm : ‖q‖ ≤ h / normalizedSectionWidthConstant n a b θ :=
    (hedeep (e x) (mem_image_of_mem e hx) (by simpa only [e.symm_apply_apply] using hdepth)).2 q hq
  have hinner : inner ℝ q (e y - e x) = inner ℝ p (y - x) := by
    dsimp [q]
    rw [LinearMap.adjoint_inner_left, map_sub]
    have hlin (z : Space n) : e.symm.linear (e z) = z - e.symm 0 := by
      have heq := continuousAffineEquiv_apply_eq_linear_add e.symm (e z)
      rw [e.symm_apply_apply] at heq
      exact eq_sub_of_add_eq heq.symm
    change inner ℝ p (e.symm.linear (e y) - e.symm.linear (e x)) = inner ℝ p (y - x)
    rw [hlin, hlin, sub_sub_sub_cancel_right]
  have hxd : ‖e x‖ ≤ 2 * ((n : ℝ) + 1) ^ 3 := by
    simpa only [mem_closedBall, dist_zero_right] using heouter (mem_image_of_mem e hx)
  have hyd : ‖e y‖ ≤ 2 * ((n : ℝ) + 1) ^ 3 := by
    simpa only [mem_closedBall, dist_zero_right] using heouter (mem_image_of_mem e hy)
  have hdist : ‖e y - e x‖ ≤ 4 * ((n : ℝ) + 1) ^ 3 := by
    have hh := norm_sub_le (e y) (e x)
    linarith
  have hη := normalizedSectionWidthConstant_pos hn ha hatop hb hbtop hθ
  have hprod : ‖q‖ * ‖e y - e x‖ ≤
      (h / normalizedSectionWidthConstant n a b θ) * (4 * ((n : ℝ) + 1) ^ 3) :=
    mul_le_mul hqnorm hdist (norm_nonneg _) (div_nonneg hh.le hη.le)
  have hip : -inner ℝ p (y - x) ≤
      (h / normalizedSectionWidthConstant n a b θ) * (4 * ((n : ℝ) + 1) ^ 3) := by
    rw [← hinner]
    exact (neg_le_abs _).trans ((abs_real_inner_le_norm _ _).trans hprod)
  have hxlow := (hosc x hx).1
  have hyupper := (hosc y hy).2
  calc
    _ ≤ h + (h / normalizedSectionWidthConstant n a b θ) * (4 * ((n : ℝ) + 1) ^ 3) := by linarith
    _ = sectionEngulfingConstant n a b θ * h := by unfold sectionEngulfingConstant; ring

end KLS
end

#print axioms KLS.sectionEngulfingConstant_pos
#print axioms KLS.support_deficit_le_sectionEngulfingConstant

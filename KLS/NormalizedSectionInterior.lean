import KLS.SectionWidthLowerBound

/-! Quantitative interior balls and actual supporting-slope bounds in one
normalized Alexandrov section. These are one-section estimates. They do not
assume or assert a Hölder modulus across different section heights. -/

open MeasureTheory InnerProductSpace Set Filter Metric
open scoped Topology NNReal ENNReal

noncomputable section
namespace KLS

variable {n : ℕ}

/-- A positive lower bound on every supporting directional width contains the
corresponding closed Euclidean ball. Separation is applied only to the actual
closed convex body. -/
theorem closedBall_subset_of_directional_width_lower
    {K : Set (Space n)} (hK : IsClosed K) (hc : Convex ℝ K)
    {x : Space n} (hx : x ∈ K) {η : ℝ} (_hη : 0 < η)
    (hwidth : ∀ (v : Space n) (δ : ℝ), ‖v‖ = 1 → 0 < δ →
      (∀ z ∈ K, inner ℝ v (z - x) ≤ δ) → η ≤ δ) :
    closedBall x η ⊆ K := by
  intro y hy
  by_contra hyK
  obtain ⟨f, c, hfK, hfy⟩ := geometric_hahn_banach_closed_point hc hK hyK
  let w : Space n := (InnerProductSpace.toDual ℝ (Space n)).symm f
  have hwrepr (z : Space n) : inner ℝ w z = f z := InnerProductSpace.toDual_symm_apply
  have hwne : w ≠ 0 := by
    intro hw
    have hfx := hwrepr x
    have hfy' := hwrepr y
    rw [hw, inner_zero_left] at hfx hfy'
    have hcx := hfK x hx
    linarith
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hwne
  let v : Space n := ‖w‖⁻¹ • w
  have hv : ‖v‖ = 1 := by
    simp only [v, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hwn)]
    exact inv_mul_cancel₀ hwn.ne'
  let δ : ℝ := (c - f x) / ‖w‖
  have hδ : 0 < δ := div_pos (sub_pos.mpr (hfK x hx)) hwn
  have hinner (z : Space n) : inner ℝ v (z - x) = (f z - f x) / ‖w‖ := by
    simp only [v, real_inner_smul_left, inner_sub_right, hwrepr, div_eq_mul_inv]
    ring
  have hcap : ∀ z ∈ K, inner ℝ v (z - x) ≤ δ := by
    intro z hz
    rw [hinner]
    exact div_le_div_of_nonneg_right (by linarith [hfK z hz]) hwn.le
  have hlower := hwidth v δ hv hδ hcap
  have hupper : inner ℝ v (y - x) ≤ η := by
    have hyn : ‖y - x‖ ≤ η := hy
    calc
      _ ≤ ‖v‖ * ‖y - x‖ := real_inner_le_norm _ _
      _ = ‖y - x‖ := by rw [hv, one_mul]
      _ ≤ η := hyn
  have hstrict : δ < inner ℝ v (y - x) := by
    rw [hinner]
    exact (div_lt_div_iff_of_pos_right hwn).mpr (by linarith)
  linarith

/-- One affine normalization gives an explicit interior ball and bounds every
actual support slope at every point of fixed relative depth. All constants
come from the dimension and the positive finite Alexandrov bounds. -/
theorem exists_normalization_with_deep_interior_ball_and_slope_bound
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
      volume (convexSubgradientImage u S) ≤ b * volume S) :
    ∃ e : Space n ≃ᴬ[ℝ] Space n,
      closedBall 0 1 ⊆ e '' K ∧
      e '' K ⊆ closedBall 0 (2 * ((n : ℝ) + 1) ^ 3) ∧
      ∀ x ∈ e '' K, θ * h ≤ -u (e.symm x) →
        closedBall x (normalizedSectionWidthConstant n a b θ) ⊆ e '' K ∧
        ∀ p ∈ convexSubgradient (fun z => u (e.symm z)) x,
          ‖p‖ ≤ h / normalizedSectionWidthConstant n a b θ := by
  obtain ⟨e, heinner, heouter, hewidth⟩ :=
    exists_normalization_with_positive_directional_width hn ha hatop hb hbtop hθ
      hK hc hne hucont huconvex hboundary hh hosc hlower hupper
  refine ⟨e, heinner, heouter, ?_⟩
  intro x hx hdepth
  have hη := normalizedSectionWidthConstant_pos hn ha hatop hb hbtop hθ
  have hball : closedBall x (normalizedSectionWidthConstant n a b θ) ⊆ e '' K :=
    closedBall_subset_of_directional_width_lower (hK.image e.continuous).isClosed
      (Convex.affine_image e.toAffineEquiv.toAffineMap hc) hx hη
      (fun v δ hv hδ hcap => hewidth x v δ hx hdepth hv hδ hcap)
  refine ⟨hball, ?_⟩
  intro p hp
  apply norm_subgradient_le_of_ball_oscillation hp hη hh.le
  intro y hy
  have hxK : e.symm x ∈ K := by
    rcases hx with ⟨z, hz, rfl⟩
    simpa only [e.symm_apply_apply] using hz
  have hyK : e.symm y ∈ K := by
    rcases hball hy with ⟨z, hz, rfl⟩
    simpa only [e.symm_apply_apply] using hz
  have hxlow := (hosc _ hxK).1
  have hyupper := (hosc _ hyK).2
  linarith

end KLS
end

#print axioms KLS.closedBall_subset_of_directional_width_lower
#print axioms KLS.exists_normalization_with_deep_interior_ball_and_slope_bound

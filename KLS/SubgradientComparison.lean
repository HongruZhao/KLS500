import KLS.ConvexSubgradient

/-!
# Geometric subgradient comparison

A support plane of the upper function at a strict comparison point can be
lowered until it touches the lower convex function at an interior strict
comparison point. Compact minimization supplies the contact point.
-/

open MeasureTheory Filter Set
open scoped Topology NNReal

noncomputable section
namespace KLS

/-- Compact support-plane sliding. Boundary ordering forces the contact point
into the interior, where convexity upgrades the local support to global support. -/
theorem exists_subgradient_contact_in_strict_comparison
    {n : ℕ} {u v : Space n → ℝ} {K : Set (Space n)} (hK : IsCompact K)
    (hucont : Continuous u) (huconvex : ConvexOn ℝ Set.univ u)
    (hboundary : ∀ z ∈ frontier K, v z ≤ u z)
    {x p : Space n} (hx : x ∈ K) (hstrict : u x < v x)
    (hp : p ∈ convexSubgradient v x) :
    ∃ z ∈ interior K, u z < v z ∧ p ∈ convexSubgradient u z := by
  let F : Space n → ℝ := fun z => u z - inner ℝ p z
  have hFcont : Continuous F := hucont.sub (continuous_const.inner continuous_id)
  obtain ⟨z, hzK, hmin⟩ := hK.exists_isMinOn ⟨x, hx⟩ hFcont.continuousOn
  have hzle := hmin hx
  have hsupport := hp z
  rw [inner_sub_right] at hsupport
  have hzstrict : u z < v z := by
    change u z - inner ℝ p z ≤ u x - inner ℝ p x at hzle
    linarith
  have hzint : z ∈ interior K := by
    by_contra hznot
    have hzb := hboundary z ((mem_frontier_iff_notMem_interior hzK).mpr hznot)
    linarith
  have hFconvex : ConvexOn ℝ Set.univ F :=
    huconvex.sub ((innerSL ℝ p).toLinearMap.concaveOn convex_univ)
  have hglobal := IsMinOn.of_isLocalMin_of_convex_univ
    (hmin.isLocalMin (mem_interior_iff_mem_nhds.mp hzint)) hFconvex
  refine ⟨z, hzint, hzstrict, ?_⟩
  intro y
  have hh := hglobal y
  change u z - inner ℝ p z ≤ u y - inner ℝ p y at hh
  rw [inner_sub_right]
  linarith

/-- Reverse inclusion of subgradient images on the strict comparison region.
It is the geometric core of Alexandrov's comparison principle. -/
theorem convexSubgradientImage_strict_comparison_subset
    {n : ℕ} {u v : Space n → ℝ} {K : Set (Space n)} (hK : IsCompact K)
    (hucont : Continuous u) (huconvex : ConvexOn ℝ Set.univ u)
    (hboundary : ∀ z ∈ frontier K, v z ≤ u z) :
    convexSubgradientImage v {x | x ∈ K ∧ u x < v x} ⊆
      convexSubgradientImage u {x | x ∈ interior K ∧ u x < v x} := by
  rintro p ⟨x, ⟨hx, hstrict⟩, hp⟩
  obtain ⟨z, hzint, hzstrict, hzp⟩ := exists_subgradient_contact_in_strict_comparison
    hK hucont huconvex hboundary hx hstrict hp
  exact ⟨z, ⟨hzint, hzstrict⟩, hzp⟩

/-- A negative interior value with nonnegative boundary values forces a whole
ball of supporting slopes. This is an elementary Alexandrov maximum estimate. -/
theorem ball_subset_convexSubgradientImage_of_negative_value
    {n : ℕ} {u : Space n → ℝ} {K : Set (Space n)} (hK : IsCompact K)
    (hucont : Continuous u) (huconvex : ConvexOn ℝ Set.univ u)
    (hboundary : ∀ z ∈ frontier K, 0 ≤ u z)
    {x : Space n} (hx : x ∈ K) (_hux : u x < 0) {R : ℝ} (hR : 0 < R)
    (hRbound : ∀ z ∈ K, ‖z - x‖ ≤ R) :
    Metric.ball 0 (-u x / R) ⊆ convexSubgradientImage u (interior K) := by
  intro p hp
  have hpR : ‖p‖ * R < -u x := by
    apply (lt_div_iff₀ hR).mp
    simpa only [Metric.mem_ball, dist_zero_right] using hp
  let v : Space n → ℝ := fun z => inner ℝ p (z - x) - R * ‖p‖
  have hvboundary : ∀ z ∈ frontier K, v z ≤ u z := by
    intro z hz
    have hzK : z ∈ K := hK.isClosed.closure_eq ▸ frontier_subset_closure hz
    have hinner : inner ℝ p (z - x) ≤ ‖p‖ * R :=
      (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hRbound z hzK) (norm_nonneg _))
    dsimp [v]
    nlinarith [hboundary z hz]
  have hstrict : u x < v x := by
    simp only [v, sub_self, inner_zero_right, zero_sub]
    nlinarith
  have hpsupport : p ∈ convexSubgradient v x := by
    intro z
    simp only [v, sub_self, inner_zero_right, zero_sub]
    linarith
  obtain ⟨z, hz, _, hpz⟩ := exists_subgradient_contact_in_strict_comparison
    hK hucont huconvex hvboundary hx hstrict hpsupport
  exact ⟨z, hz, hpz⟩

/-- Explicit volume form of the preceding geometric maximum estimate. -/
theorem volume_ball_le_convexSubgradientImage_of_negative_value
    {n : ℕ} {u : Space n → ℝ} {K : Set (Space n)} (hK : IsCompact K)
    (hucont : Continuous u) (huconvex : ConvexOn ℝ Set.univ u)
    (hboundary : ∀ z ∈ frontier K, 0 ≤ u z)
    {x : Space n} (hx : x ∈ K) (_hux : u x < 0) {R : ℝ} (hR : 0 < R)
    (hRbound : ∀ z ∈ K, ‖z - x‖ ≤ R) :
    volume (Metric.ball (0 : Space n) (-u x / R)) ≤
      volume (convexSubgradientImage u (interior K)) :=
  measure_mono (ball_subset_convexSubgradientImage_of_negative_value
    hK hucont huconvex hboundary hx _hux hR hRbound)

end KLS
end

#print axioms KLS.exists_subgradient_contact_in_strict_comparison
#print axioms KLS.convexSubgradientImage_strict_comparison_subset

#print axioms KLS.ball_subset_convexSubgradientImage_of_negative_value

import KLS.MomentLegendreDomainSupport
import KLS.MomentPotentialSublevel

/-! Bounded centered sections for interior slopes of the actual finite
conjugate domain.  Compactness comes from an explicit linear growth estimate
for the tilted potential, not from a regularity assumption. -/

open MeasureTheory InnerProductSpace Set Filter Metric
open scoped Topology NNReal ENNReal

noncomputable section
namespace KLS

variable {n : ℕ}

def tiltedPotential (φ : Space n → ℝ) (p : Space n) : Space n → ℝ :=
  fun x => φ x - inner ℝ p x

theorem continuous_tiltedPotential {φ : Space n → ℝ} (hφ : Continuous φ) (p : Space n) :
    Continuous (tiltedPotential φ p) := hφ.sub (continuous_const.inner continuous_id)

theorem convexOn_tiltedPotential {φ : Space n → ℝ}
    (hφ : ConvexOn ℝ univ φ) (p : Space n) : ConvexOn ℝ univ (tiltedPotential φ p) :=
  hφ.sub ((innerSL ℝ p).toLinearMap.concaveOn convex_univ)

/-- Interior finiteness of the conjugate gives actual positive linear growth
of the tilted potential in every direction. -/
theorem exists_linear_lower_bound_tiltedPotential
    (φ : Space n → ℝ) {p : Space n} (hp : p ∈ interior (momentLegendreDomain φ)) :
    ∃ r M : ℝ, 0 < r ∧ ∀ x, r * ‖x‖ - M ≤ tiltedPotential φ p x := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hp)
  let r : ℝ := ε / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hclosed : closedBall p r ⊆ interior (momentLegendreDomain φ) :=
    (closedBall_subset_ball (by dsimp [r]; linarith : r < ε)).trans hball
  have hcont := (convexOn_normalizedLegendreTransform_toReal φ).continuousOn_interior.mono hclosed
  obtain ⟨M, hM⟩ := (isCompact_closedBall p r).bddAbove_image hcont
  refine ⟨r, M, hr, ?_⟩
  intro x
  by_cases hx : x = 0
  · have hMp : (normalizedLegendreTransform φ p).toReal ≤ M :=
      hM ⟨p, mem_closedBall_self hr.le, rfl⟩
    have hy := normalizedLegendreTransform_young φ (interior_subset hp) (0 : Space n)
    simp only [inner_zero_right] at hy
    simp only [hx, norm_zero, mul_zero, zero_sub, tiltedPotential, inner_zero_right, sub_zero]
    linarith
  · have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx
    let q : Space n := p + (r / ‖x‖) • x
    have hqp : ‖q - p‖ = r := by
      simp only [q, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos (div_pos hr hnx), div_mul_cancel₀ _ hnx.ne']
    have hqball : q ∈ closedBall p r := by
      simpa only [mem_closedBall, dist_eq_norm, hqp] using (le_rfl : r ≤ r)
    have hqD := interior_subset (hclosed hqball)
    have hMq : (normalizedLegendreTransform φ q).toReal ≤ M := hM ⟨q, hqball, rfl⟩
    have hy := normalizedLegendreTransform_young φ hqD x
    have hqx : inner ℝ q x = inner ℝ p x + r * ‖x‖ := by
      simp only [q, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
      field_simp
    rw [hqx] at hy
    dsimp [tiltedPotential]
    linarith

theorem isCompact_sublevel_tiltedPotential {φ : Space n → ℝ} (hφ : Continuous φ)
    {p : Space n} (hp : p ∈ interior (momentLegendreDomain φ)) (a : ℝ) :
    IsCompact {x | tiltedPotential φ p x ≤ a} := by
  obtain ⟨r, M, hr, hgrowth⟩ := exists_linear_lower_bound_tiltedPotential φ hp
  refine isCompact_iff_isClosed_bounded.mpr
    ⟨isClosed_le (continuous_tiltedPotential hφ p) continuous_const, ?_⟩
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨(a + M) / r, ?_⟩
  intro x hx
  apply (le_div_iff₀ hr).mpr
  have hh := hgrowth x
  change tiltedPotential φ p x ≤ a at hx
  nlinarith

theorem tendsto_tiltedPotential_cocompact_atTop {φ : Space n → ℝ} (hφ : Continuous φ)
    {p : Space n} (hp : p ∈ interior (momentLegendreDomain φ)) :
    Tendsto (tiltedPotential φ p) (cocompact (Space n)) atTop := by
  apply Filter.tendsto_atTop.2
  intro a
  filter_upwards [(isCompact_sublevel_tiltedPotential hφ hp a).compl_mem_cocompact] with x hx
  exact (lt_of_not_ge (show ¬tiltedPotential φ p x ≤ a from hx)).le

/-- Every interior slope is attained by an ordinary subgradient at a finite
source point. -/
theorem exists_mem_convexSubgradient_of_mem_interior_momentLegendreDomain
    {φ : Space n → ℝ} (hφ : Continuous φ)
    {p : Space n} (hp : p ∈ interior (momentLegendreDomain φ)) :
    ∃ x, p ∈ convexSubgradient φ x := by
  obtain ⟨x, hx⟩ := (continuous_tiltedPotential hφ p).exists_forall_le
    (tendsto_tiltedPotential_cocompact_atTop hφ hp)
  refine ⟨x, ?_⟩
  intro y
  have hh := hx y
  dsimp [tiltedPotential] at hh
  rw [inner_sub_right]
  linarith

def centeredSection (φ : Space n → ℝ) (x p : Space n) (a : ℝ) : Set (Space n) :=
  {y | φ y < φ x + inner ℝ p (y - x) + a}

theorem centeredSection_eq_tilted_sublevel (φ : Space n → ℝ) (x p : Space n) (a : ℝ) :
    centeredSection φ x p a = potentialSublevel (tiltedPotential φ p)
      (tiltedPotential φ p x + a) := by
  ext y
  simp only [centeredSection, potentialSublevel, tiltedPotential, mem_ofPred_eq, inner_sub_right]
  constructor <;> intro h <;> linarith

theorem isOpen_centeredSection {φ : Space n → ℝ} (hφ : Continuous φ) (x p : Space n) (a : ℝ) :
    IsOpen (centeredSection φ x p a) := by
  rw [centeredSection_eq_tilted_sublevel]
  exact isOpen_potentialSublevel (continuous_tiltedPotential hφ p) _

theorem convex_centeredSection {φ : Space n → ℝ} (hc : ConvexOn ℝ univ φ)
    (x p : Space n) (a : ℝ) : Convex ℝ (centeredSection φ x p a) := by
  rw [centeredSection_eq_tilted_sublevel]
  exact convex_potentialSublevel (convexOn_tiltedPotential hc p) _

theorem isCompact_closure_centeredSection {φ : Space n → ℝ} (hφ : Continuous φ)
    {p : Space n} (hp : p ∈ interior (momentLegendreDomain φ)) (x : Space n) (a : ℝ) :
    IsCompact (closure (centeredSection φ x p a)) := by
  rw [centeredSection_eq_tilted_sublevel]
  exact (isCompact_sublevel_tiltedPotential hφ hp _).of_isClosed_subset
    isClosed_closure (closure_lt_subset_le (continuous_tiltedPotential hφ p) continuous_const)

theorem potential_eq_support_add_height_on_frontier_centeredSection
    {φ : Space n → ℝ} (hφ : Continuous φ) (x p : Space n) (a : ℝ) {y : Space n}
    (hy : y ∈ frontier (centeredSection φ x p a)) :
    φ y = φ x + inner ℝ p (y - x) + a := by
  exact frontier_lt_subset_eq hφ
    (continuous_const.add (continuous_const.inner (continuous_id.sub continuous_const)) |>.add
      continuous_const) hy

end KLS
end

#print axioms KLS.exists_linear_lower_bound_tiltedPotential
#print axioms KLS.exists_mem_convexSubgradient_of_mem_interior_momentLegendreDomain
#print axioms KLS.isCompact_closure_centeredSection

import KLS.SectionEngulfing
import KLS.MomentCenteredSections

/-! The quantitative engulfing inequality applied to the actual closed
sections cut out by support planes of the original potential. -/

open MeasureTheory InnerProductSpace Set Filter Metric
open scoped Topology NNReal ENNReal

noncomputable section
namespace KLS

variable {n : ℕ}

def closedCenteredSection (u : Space n → ℝ) (x p : Space n) (h : ℝ) : Set (Space n) :=
  {y | u y ≤ u x + inner ℝ p (y - x) + h}

def centeredSectionPotential (u : Space n → ℝ) (x p : Space n) (h : ℝ) : Space n → ℝ :=
  fun y => u y - u x - inner ℝ p (y - x) - h

theorem centeredSectionPotential_eq_add_affine
    (u : Space n → ℝ) (x p : Space n) (h : ℝ) :
    centeredSectionPotential u x p h =
      fun y => u y + inner ℝ (-p) y + (inner ℝ p x - u x - h) := by
  funext y
  simp only [centeredSectionPotential, inner_neg_left, inner_sub_right]
  ring

theorem closedCenteredSection_eq_tilted_sublevel
    (u : Space n → ℝ) (x p : Space n) (h : ℝ) :
    closedCenteredSection u x p h = {y | tiltedPotential u p y ≤ tiltedPotential u p x + h} := by
  ext y
  simp only [closedCenteredSection, tiltedPotential, mem_ofPred_eq, inner_sub_right]
  constructor <;> intro hh <;> linarith

theorem closedCenteredSection_eq_sectionPotential_sublevel
    (u : Space n → ℝ) (x p : Space n) (h : ℝ) :
    closedCenteredSection u x p h = {y | centeredSectionPotential u x p h y ≤ 0} := by
  ext y
  simp only [closedCenteredSection, centeredSectionPotential, mem_ofPred_eq]
  constructor <;> intro hh <;> linarith

theorem continuous_centeredSectionPotential
    {u : Space n → ℝ} (hu : Continuous u) (x p : Space n) (h : ℝ) :
    Continuous (centeredSectionPotential u x p h) := by
  exact ((hu.sub continuous_const).sub
    (continuous_const.inner (continuous_id.sub continuous_const))).sub continuous_const

theorem convexOn_centeredSectionPotential
    {u : Space n → ℝ} (hu : ConvexOn ℝ univ u) (x p : Space n) (h : ℝ) :
    ConvexOn ℝ univ (centeredSectionPotential u x p h) := by
  rw [centeredSectionPotential_eq_add_affine]
  exact (hu.add ((innerSL ℝ (-p)).toLinearMap.convexOn convex_univ)).add_const _

theorem isCompact_closedCenteredSection
    {u : Space n → ℝ} (hu : Continuous u) {p : Space n}
    (hp : p ∈ interior (momentLegendreDomain u)) (x : Space n) (h : ℝ) :
    IsCompact (closedCenteredSection u x p h) := by
  rw [closedCenteredSection_eq_tilted_sublevel]
  exact isCompact_sublevel_tiltedPotential hu hp _

theorem convex_closedCenteredSection
    {u : Space n → ℝ} (hu : ConvexOn ℝ univ u) (x p : Space n) (h : ℝ) :
    Convex ℝ (closedCenteredSection u x p h) := by
  rw [closedCenteredSection_eq_sectionPotential_sublevel]
  convert (convexOn_centeredSectionPotential hu x p h).convex_le 0 using 1
  ext y
  simp only [mem_univ, true_and]

theorem self_mem_interior_closedCenteredSection
    {u : Space n → ℝ} (hu : Continuous u) (x p : Space n) {h : ℝ} (hh : 0 < h) :
    x ∈ interior (closedCenteredSection u x p h) := by
  apply mem_interior_iff_mem_nhds.mpr
  apply mem_of_superset ((isOpen_centeredSection hu x p h).mem_nhds ?_)
  · intro y hy
    change u y < u x + inner ℝ p (y - x) + h at hy
    exact hy.le
  · change u x < u x + inner ℝ p (x - x) + h
    simp only [sub_self, inner_zero_right, add_zero]
    linarith

theorem volume_convexSubgradientImage_centeredSectionPotential
    (u : Space n → ℝ) (x p : Space n) (h : ℝ) (S : Set (Space n)) :
    volume (convexSubgradientImage (centeredSectionPotential u x p h) S) =
      volume (convexSubgradientImage u S) := by
  rw [centeredSectionPotential_eq_add_affine, volume_convexSubgradientImage_add_affine]

/-- Every closed section is contained in a uniformly enlarged section based
at any point in its smaller concentric section. The bound concerns all actual
support slopes, so no differentiability is assumed. -/
theorem closedCenteredSection_subset_recentered
    (hn : 0 < n) {a b : ℝ≥0∞}
    (ha : 0 < a) (hatop : a < ∞) (hb : 0 < b) (hbtop : b < ∞)
    {θ : ℝ} (hθ : 0 < θ) {u : Space n → ℝ}
    (hu : Continuous u) (hc : ConvexOn ℝ univ u)
    {x₀ p₀ : Space n} (hp₀ : p₀ ∈ convexSubgradient u x₀)
    (hpD : p₀ ∈ interior (momentLegendreDomain u)) {h : ℝ} (hh : 0 < h)
    (hlower : ∀ S : Set (Space n), IsCompact S → S ⊆ closedCenteredSection u x₀ p₀ h →
      a * volume S ≤ volume (convexSubgradientImage u S))
    (hupper : ∀ S : Set (Space n), IsOpen S → S ⊆ closedCenteredSection u x₀ p₀ h →
      volume (convexSubgradientImage u S) ≤ b * volume S)
    {x p : Space n} (hx : x ∈ closedCenteredSection u x₀ p₀ ((1 - θ) * h))
    (hp : p ∈ convexSubgradient u x) :
    closedCenteredSection u x₀ p₀ h ⊆
      closedCenteredSection u x p (sectionEngulfingConstant n a b θ * h) := by
  let f := centeredSectionPotential u x₀ p₀ h
  let K := closedCenteredSection u x₀ p₀ h
  have hf : Continuous f := continuous_centeredSectionPotential hu x₀ p₀ h
  have hfc : ConvexOn ℝ univ f := convexOn_centeredSectionPotential hc x₀ p₀ h
  have hKeq : K = {y | f y ≤ 0} := closedCenteredSection_eq_sectionPotential_sublevel u x₀ p₀ h
  have hKc : IsCompact K := isCompact_closedCenteredSection hu hpD x₀ h
  have hKconv : Convex ℝ K := convex_closedCenteredSection hc x₀ p₀ h
  have hKint : (interior K).Nonempty := ⟨x₀, self_mem_interior_closedCenteredSection hu x₀ p₀ hh⟩
  have hboundary : ∀ z ∈ frontier K, 0 ≤ f z := by
    intro z hz
    rw [hKeq] at hz
    exact (frontier_le_subset_eq hf continuous_const hz).ge
  have hosc : ∀ z ∈ K, -h ≤ f z ∧ f z ≤ 0 := by
    intro z hz
    have hs := hp₀ z
    change u z ≤ u x₀ + inner ℝ p₀ (z - x₀) + h at hz
    dsimp [f, centeredSectionPotential]
    constructor <;> linarith
  have hxK : x ∈ K := by
    change u x ≤ u x₀ + inner ℝ p₀ (x - x₀) + h
    change u x ≤ u x₀ + inner ℝ p₀ (x - x₀) + (1 - θ) * h at hx
    nlinarith [mul_pos hθ hh]
  have hdepth : θ * h ≤ -f x := by
    change u x ≤ u x₀ + inner ℝ p₀ (x - x₀) + (1 - θ) * h at hx
    dsimp [f, centeredSectionPotential]
    nlinarith
  have hpf : p - p₀ ∈ convexSubgradient f x := by
    intro y
    have hy := hp y
    dsimp [f, centeredSectionPotential]
    simp only [inner_sub_left, inner_sub_right] at hy ⊢
    linarith
  have hlowerf : ∀ S : Set (Space n), IsCompact S → S ⊆ K →
      a * volume S ≤ volume (convexSubgradientImage f S) := by
    intro S hS hSK
    rw [volume_convexSubgradientImage_centeredSectionPotential]
    exact hlower S hS hSK
  have hupperf : ∀ S : Set (Space n), IsOpen S → S ⊆ K →
      volume (convexSubgradientImage f S) ≤ b * volume S := by
    intro S hS hSK
    rw [volume_convexSubgradientImage_centeredSectionPotential]
    exact hupper S hS hSK
  intro y hy
  have hbound := support_deficit_le_sectionEngulfingConstant hn ha hatop hb hbtop hθ
    hKc hKconv hKint hf hfc hboundary hh hosc hlowerf hupperf hxK hy hdepth hpf
  change u y ≤ u x + inner ℝ p (y - x) + sectionEngulfingConstant n a b θ * h
  dsimp [f, centeredSectionPotential] at hbound
  simp only [inner_sub_left, inner_sub_right] at hbound ⊢
  linarith

end KLS
end

#print axioms KLS.isCompact_closedCenteredSection
#print axioms KLS.self_mem_interior_closedCenteredSection
#print axioms KLS.closedCenteredSection_subset_recentered

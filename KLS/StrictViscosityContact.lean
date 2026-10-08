import KLS.NormalizedMongeAmpereViscosity

/-! Actual transfer of touching tests to a uniformly nearby continuous
function, by maximization on a compact neighborhood. -/
open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff RealInnerProductSpace NNReal Matrix.Norms.Elementwise
noncomputable section
namespace KLS
variable {n : ℕ}

theorem exists_interior_upper_contact_of_uniform_bound
    {u v ψ : Space n → ℝ} (hv : Continuous v) (hψ : Continuous ψ)
    {K : Set (Space n)} (hK : IsCompact K) {x₀ : Space n} (hx₀ : x₀ ∈ K)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ x ∈ frontier K, u x - ψ x ≤ u x₀ - ψ x₀ - δ)
    (hclose : ∀ x ∈ K, |v x - u x| ≤ δ / 3) :
    ∃ z ∈ interior K, ∃ a : ℝ,
      v z = ψ z + a ∧ (∀ᶠ y in 𝓝 z, v y ≤ ψ y + a) := by
  obtain ⟨z, hz, hmax⟩ := hK.exists_isMaxOn ⟨x₀, hx₀⟩ (hv.sub hψ).continuousOn
  have hzint : z ∈ interior K := by
    by_contra hn
    have hb := hgap z ((mem_frontier_iff_notMem_interior hz).mpr hn)
    have hc₀ := (abs_le.mp (hclose x₀ hx₀)).1
    have hcz := (abs_le.mp (hclose z hz)).2
    have hm := hmax hx₀
    change v x₀ - ψ x₀ ≤ v z - ψ z at hm
    linarith
  refine ⟨z, hzint, v z - ψ z, by ring, ?_⟩
  filter_upwards [mem_interior_iff_mem_nhds.mp hzint] with y hy
  have hm := hmax hy
  change v y - ψ y ≤ v z - ψ z at hm
  linarith

theorem exists_interior_lower_contact_of_uniform_bound
    {u v ψ : Space n → ℝ} (hv : Continuous v) (hψ : Continuous ψ)
    {K : Set (Space n)} (hK : IsCompact K) {x₀ : Space n} (hx₀ : x₀ ∈ K)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ x ∈ frontier K, ψ x - u x ≤ ψ x₀ - u x₀ - δ)
    (hclose : ∀ x ∈ K, |v x - u x| ≤ δ / 3) :
    ∃ z ∈ interior K, ∃ a : ℝ,
      v z = ψ z + a ∧ (∀ᶠ y in 𝓝 z, ψ y + a ≤ v y) := by
  obtain ⟨z, hz, a, hc, ht⟩ := exists_interior_upper_contact_of_uniform_bound
    (u := -u) (v := -v) (ψ := -ψ) hv.neg hψ.neg hK hx₀ hδ
    (fun x hx => by simpa only [Pi.neg_apply, neg_sub_neg] using hgap x hx)
    (fun x hx => by simpa only [Pi.neg_apply, neg_sub_neg, abs_sub_comm] using hclose x hx)
  refine ⟨z, hz, -a, ?_, ?_⟩
  · change -v z = -ψ z + a at hc
    linarith
  · filter_upwards [ht] with y hy
    change -v y ≤ -ψ y + a at hy
    linarith

end KLS
end

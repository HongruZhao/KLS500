import KLS.StrictAlexandrovComparison

/-! Strict boundary comparison remains strict throughout a compact set.
Constant shifts preserve the actual support-plane image. -/

open MeasureTheory Set Filter
open scoped Topology ENNReal

noncomputable section
namespace KLS

private lemma subgradientImage_sub_constant {n : ℕ} (u : Space n → ℝ)
    (d : ℝ) (S : Set (Space n)) :
    convexSubgradientImage (fun x => u x - d) S = convexSubgradientImage u S := by
  ext p
  constructor <;> rintro ⟨x, hx, hp⟩ <;> refine ⟨x, hx, ?_⟩ <;>
    intro y <;> have h := hp y <;> dsimp only at h ⊢ <;> linarith

lemma exists_pos_uniform_gap_on_compact
    {n : ℕ} {u v : Space n → ℝ} {K : Set (Space n)}
    (hK : IsCompact K) (hu : Continuous u) (hv : Continuous v)
    (hstrict : ∀ x ∈ K, v x < u x) :
    ∃ d > 0, ∀ x ∈ K, v x ≤ u x - d := by
  by_cases hne : K.Nonempty
  · obtain ⟨z, hz, hmin⟩ := hK.exists_isMinOn hne (hu.sub hv).continuousOn
    refine ⟨(u z - v z) / 2, by linarith [hstrict z hz], ?_⟩
    intro x hx
    have hh := hmin hx
    change u z - v z ≤ u x - v x at hh
    linarith [hstrict z hz]
  · exact ⟨1, by norm_num, fun x hx => (hne ⟨x, hx⟩).elim⟩

theorem lt_of_strict_subgradient_volume_comparison
    {n : ℕ} {u v : Space n → ℝ} {K : Set (Space n)}
    (hK : IsCompact K) (hu : Continuous u) (hv : Continuous v)
    (huc : ConvexOn ℝ univ u)
    (hboundary : ∀ x ∈ frontier K, v x < u x)
    {a b : ℝ≥0∞} (hab : a < b)
    (hmass : ∀ S : Set (Space n), IsOpen S → S ⊆ K →
      volume (convexSubgradientImage u S) ≤ a * volume S ∧
      b * volume S ≤ volume (convexSubgradientImage v S)) :
    ∀ x ∈ K, v x < u x := by
  have hfront : IsCompact (frontier K) :=
    hK.of_isClosed_subset isClosed_frontier (fun _ hx =>
      hK.isClosed.closure_eq ▸ frontier_subset_closure hx)
  obtain ⟨d, hd, hgap⟩ := exists_pos_uniform_gap_on_compact hfront hu hv hboundary
  have hcshift : ConvexOn ℝ univ (fun x => u x - d) := by
    convert huc.add_const (-d) using 1
  have hle := le_of_strict_subgradient_volume_comparison
    (u := fun x => u x - d) hK (hu.sub continuous_const)
    hv hcshift hgap hab (fun S hS hSK => by
      rw [subgradientImage_sub_constant]
      exact hmass S hS hSK)
  intro x hx
  linarith [hle x hx]

end KLS
end

#print axioms KLS.lt_of_strict_subgradient_volume_comparison

import KLS.SubgradientComparison
import KLS.MomentAlexandrovOpen

/-! A strict Alexandrov comparison principle proved from the actual
support-plane image inclusion and the volume of a nonempty open set. -/

open MeasureTheory Set Filter
open scoped Topology ENNReal

noncomputable section
namespace KLS

/-- A strict gap between upper and lower subgradient-volume densities prevents
an interior crossing when the functions have the prescribed boundary order. -/
theorem le_of_strict_subgradient_volume_comparison
    {n : ℕ} {u v : Space n → ℝ} {K : Set (Space n)}
    (hK : IsCompact K) (hu : Continuous u) (hv : Continuous v)
    (huc : ConvexOn ℝ univ u)
    (hboundary : ∀ x ∈ frontier K, v x ≤ u x)
    {a b : ℝ≥0∞} (hab : a < b)
    (hmass : ∀ S : Set (Space n), IsOpen S → S ⊆ K →
      volume (convexSubgradientImage u S) ≤ a * volume S ∧
      b * volume S ≤ volume (convexSubgradientImage v S)) :
    ∀ x ∈ K, v x ≤ u x := by
  intro x hx
  by_contra hnot
  have hstrict : u x < v x := lt_of_not_ge hnot
  let S : Set (Space n) := {z | z ∈ interior K ∧ u z < v z}
  have hSopen : IsOpen S := isOpen_interior.inter (isOpen_lt hu hv)
  have hSK : S ⊆ K := fun _ hz => interior_subset hz.1
  have hxint : x ∈ interior K := by
    by_contra hni
    exact (not_le_of_gt hstrict) (hboundary x ((mem_frontier_iff_notMem_interior hx).mpr hni))
  have hSpos : 0 < volume S := hSopen.measure_pos volume ⟨x, hxint, hstrict⟩
  have hSfin : volume S < ∞ := (measure_mono hSK).trans_lt hK.measure_lt_top
  have himage : convexSubgradientImage v S ⊆ convexSubgradientImage u S := by
    intro p hp
    apply convexSubgradientImage_strict_comparison_subset hK hu huc hboundary
    rcases hp with ⟨z, hz, hpz⟩
    exact ⟨z, ⟨interior_subset hz.1, hz.2⟩, hpz⟩
  have hm := hmass S hSopen hSK
  have hle : b * volume S ≤ a * volume S := hm.2.trans ((measure_mono himage).trans hm.1)
  exact (not_le_of_gt (ENNReal.mul_lt_mul_left hSpos.ne' hSfin.ne hab)) hle

/-- Exact open-set Monge--Ampere identities with uniformly separated
pointwise densities discharge the preceding volume hypotheses. -/
theorem le_of_strict_alexandrov_density_comparison
    {n : ℕ} {u v : Space n → ℝ} {K : Set (Space n)}
    (hK : IsCompact K) (hu : Continuous u) (hv : Continuous v)
    (huc : ConvexOn ℝ univ u)
    (hboundary : ∀ x ∈ frontier K, v x ≤ u x)
    {f g : Space n → ℝ≥0∞} {a b : ℝ≥0∞} (hab : a < b)
    (hf : ∀ x ∈ K, f x ≤ a) (hg : ∀ x ∈ K, b ≤ g x)
    (huMA : ∀ S : Set (Space n), IsOpen S → S ⊆ K →
      volume (convexSubgradientImage u S) = ∫⁻ x in S, f x ∂volume)
    (hvMA : ∀ S : Set (Space n), IsOpen S → S ⊆ K →
      volume (convexSubgradientImage v S) = ∫⁻ x in S, g x ∂volume) :
    ∀ x ∈ K, v x ≤ u x := by
  apply le_of_strict_subgradient_volume_comparison hK hu hv huc hboundary hab
  intro S hS hSK
  rw [huMA S hS hSK, hvMA S hS hSK]
  constructor
  · calc
      _ ≤ ∫⁻ _x in S, a ∂volume := setLIntegral_mono' hS.measurableSet
        (fun x hx => hf x (hSK hx))
      _ = _ := by simp
  · calc
      _ = ∫⁻ _x in S, b ∂volume := by simp
      _ ≤ _ := setLIntegral_mono' hS.measurableSet (fun x hx => hg x (hSK hx))

end KLS
end

#print axioms KLS.le_of_strict_subgradient_volume_comparison
#print axioms KLS.le_of_strict_alexandrov_density_comparison

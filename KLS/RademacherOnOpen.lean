import KLS.Definitions
import KLS.LocalRademacher
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Measure

/-! Local Rademacher on an actual open domain. A countable neighborhood
subcover controls the exceptional set; the function is not assumed to be
Lipschitz or even continuous outside the domain. -/

open MeasureTheory Set Filter
open scoped Topology

namespace KLS

theorem locallyLipschitzOn_ae_differentiableAt_of_isOpen
    {n : ℕ} {f : Space n → ℝ} {S : Set (Space n)}
    (hS : IsOpen S) (hf : LocallyLipschitzOn S f) :
    ∀ᵐ x ∂volume, x ∈ S → DifferentiableAt ℝ f x := by
  classical
  choose K U hU hLip using fun x : S => hf x.property
  have hUn (x : S) : U x ∈ 𝓝 (x : Space n) := by
    simpa only [nhdsWithin_eq_nhds.mpr (hS.mem_nhds x.property)] using hU x
  have hcover : S ⊆ ⋃ x : S, interior (U x) := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.mpr (hUn ⟨x, hx⟩)⟩
  obtain ⟨A, hA, hAS⟩ := (HereditarilyLindelofSpace.isLindelof S).elim_countable_subcover
    (fun x : S => interior (U x)) (fun _ => isOpen_interior) hcover
  have hlocal (z : S) : ∀ᵐ x ∂volume,
      x ∈ interior (U z) → DifferentiableAt ℝ f x := by
    filter_upwards [(hLip z).ae_differentiableWithinAt_of_mem (μ := volume)] with x hx
    intro hxin
    exact (hx (interior_subset hxin)).differentiableAt
      (mem_interior_iff_mem_nhds.mp hxin)
  filter_upwards [(ae_ball_iff hA).mpr (fun z _ => hlocal z)] with x hx
  intro hxS
  obtain ⟨z, hzA, hxz⟩ := mem_iUnion₂.mp (hAS hxS)
  exact hx z hzA hxz

theorem locallyLipschitzOn_ae_differentiableAt_of_isOpen_of_absolutelyContinuous
    {n : ℕ} {f : Space n → ℝ} {S : Set (Space n)} {μ : Measure (Space n)}
    (hμ : μ ≪ volume) (hS : IsOpen S) (hf : LocallyLipschitzOn S f) :
    ∀ᵐ x ∂μ, x ∈ S → DifferentiableAt ℝ f x :=
  hμ.ae_le (locallyLipschitzOn_ae_differentiableAt_of_isOpen hS hf)

theorem convexOn_ae_differentiableAt_interior
    {n : ℕ} {f : Space n → ℝ} {S : Set (Space n)} {μ : Measure (Space n)}
    (hμ : μ ≪ volume) (hf : ConvexOn ℝ S f) :
    ∀ᵐ x ∂μ, x ∈ interior S → DifferentiableAt ℝ f x :=
  locallyLipschitzOn_ae_differentiableAt_of_isOpen_of_absolutelyContinuous hμ
    isOpen_interior hf.locallyLipschitzOn_interior

/-- Absolute continuity removes the convex domain's boundary as well as the
Rademacher exceptional set, whenever the actual law is concentrated on the domain. -/
theorem convexOn_ae_mem_interior_and_differentiableAt
    {n : ℕ} {f : Space n → ℝ} {S : Set (Space n)} {μ : Measure (Space n)}
    (hμ : μ ≪ volume) (hf : ConvexOn ℝ S f) (hmem : ∀ᵐ x ∂μ, x ∈ S) :
    ∀ᵐ x ∂μ, x ∈ interior S ∧ DifferentiableAt ℝ f x := by
  have hfrontier : μ (frontier S) = 0 := hμ (hf.1.addHaar_frontier volume)
  filter_upwards [interior_ae_eq_of_null_frontier hfrontier,
    hmem, convexOn_ae_differentiableAt_interior hμ hf] with x hx hs hd
  have hi : x ∈ interior S := hx.mpr hs
  exact ⟨hi, hd hi⟩

end KLS

#print axioms KLS.locallyLipschitzOn_ae_differentiableAt_of_isOpen
#print axioms KLS.convexOn_ae_differentiableAt_interior
#print axioms KLS.convexOn_ae_mem_interior_and_differentiableAt

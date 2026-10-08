import KLS.MomentStrictConvexity
import KLS.MomentGradientRange
import KLS.SubgradientTransport

/-!
# Interior location of every supporting slope

Strict convexity and global subgradient containment force every supporting
slope into the interior of a convex target. A boundary supporting functional
would contradict the strict support inequality along its representing vector.
This is an interior-location result, not differentiability of the source.
-/

open MeasureTheory InnerProductSpace Set
open scoped Topology NNReal ENNReal

noncomputable section
namespace KLS

variable {n : ℕ}

theorem strict_support_inequality_of_strictConvexOn
    {u : Space n → ℝ} (hc : StrictConvexOn ℝ univ u)
    {x y p : Space n} (hp : p ∈ convexSubgradient u x) (hxy : x ≠ y) :
    u x + inner ℝ p (y - x) < u y := by
  apply lt_of_le_of_ne (hp y)
  intro heq
  have hq : p ∈ convexSubgradient u y := by
    intro z
    have hs := hp z
    simp only [inner_sub_right] at heq hs ⊢
    linarith
  exact hxy (eq_of_common_convexSubgradient hc hp hq)

/-- A global strictly convex potential cannot attain a boundary slope of
a convex set containing all of its subgradients. -/
theorem convexSubgradient_subset_interior_of_strictConvexOn
    {u : Space n → ℝ} (hu : Continuous u) (hc : StrictConvexOn ℝ univ u)
    {K : Set (Space n)} (hKc : Convex ℝ K) (hKint : (interior K).Nonempty)
    (hrange : ∀ x, convexSubgradient u x ⊆ K) (x : Space n) :
    convexSubgradient u x ⊆ interior K := by
  intro p hp
  by_contra hnot
  obtain ⟨f, hfne, hfK⟩ := geometric_hahn_banach_of_nonempty_interior_point hKc hnot hKint
  let v : Space n := (InnerProductSpace.toDual ℝ (Space n)).symm f
  have hvinner (q : Space n) : inner ℝ v q = f q := InnerProductSpace.toDual_symm_apply
  have hv : v ≠ 0 := by
    intro hzero
    apply hfne
    ext q
    have hh := hvinner q
    rw [hzero, inner_zero_left] at hh
    simpa only [zero_apply] using hh.symm
  have hxy : x ≠ x + v := by
    intro h
    apply hv
    have hh : x + v = x + 0 := by simpa using h.symm
    exact add_left_cancel hh
  obtain ⟨q, hq⟩ := convexSubgradient_nonempty hu hc.convexOn (x + v)
  have hstrict := strict_support_inequality_of_strictConvexOn hc hp hxy
  have hback := hq x
  have hslope := hfK q (hrange (x + v) hq)
  rw [← hvinner q, ← hvinner p, ← real_inner_comm v q, ← real_inner_comm v p] at hslope
  simp only [add_sub_cancel_left] at hstrict
  have hdiff : x - (x + v) = -v := by abel
  rw [hdiff, inner_neg_right] at hback
  linarith

/-- Every slope in every source subgradient lies in the actual target
interior for the weak moment transport. -/
theorem moment_convexSubgradient_subset_interior
    {φ V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L φ)
    (hc : ConvexOn ℝ univ φ) (hV : Continuous V)
    [IsFiniteMeasure (potentialMeasure φ)]
    {K : Set (Space n)} (hKclosed : IsClosed K) (hKc : Convex ℝ K)
    (hKint : (interior K).Nonempty)
    (hpush : MomentMap.gradientPushforward φ = (potentialMeasure V).restrict K)
    (x : Space n) : convexSubgradient φ x ⊆ interior K := by
  have hstrict := moment_strictConvexOn hLip hc hV hKclosed.measurableSet hKc hpush
  apply convexSubgradient_subset_interior_of_strictConvexOn hLip.continuous hstrict hKc hKint
  exact convexSubgradient_subset_of_momentMap hLip hc hpush hKclosed hKc
    (ae_restrict_mem hKclosed.measurableSet)

theorem isCompact_convexSubgradient_of_lipschitz
    {φ : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L φ) (x : Space n) :
    IsCompact (convexSubgradient φ x) := by
  have heq : convexSubgradientImage φ {x} = convexSubgradient φ x := by
    ext p
    simp only [convexSubgradientImage, mem_singleton_iff, mem_ofPred_eq, exists_eq_left]
  rw [← heq]
  exact isCompact_convexSubgradientImage hLip isCompact_singleton

end KLS
end

#print axioms KLS.strict_support_inequality_of_strictConvexOn
#print axioms KLS.convexSubgradient_subset_interior_of_strictConvexOn
#print axioms KLS.moment_convexSubgradient_subset_interior
#print axioms KLS.isCompact_convexSubgradient_of_lipschitz

import KLS.TruncatedConjugateSingleton
import KLS.CoerciveSublevelLocalization
import KLS.MomentConjugateInterior
import KLS.SingletonSubgradientDifferentiability

/-! Actual C1 regularity of a finite-mass weak moment potential with continuous
positive density on a closed convex target. A coercive finite truncation of
the genuine conjugate localizes around each original subgradient set. The
reciprocal mass equation supplies its Alexandrov bounds, and the local contact
theorem forces the original subgradient set to be a singleton. -/

open MeasureTheory InnerProductSpace Set Filter Metric
open scoped Topology NNReal ENNReal

noncomputable section
namespace KLS

variable {n : ℕ}

theorem momentLegendreDomain_subset_closedTarget
    {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) {K : Set (Space n)} (hK : IsClosed K)
    (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K) :
    momentLegendreDomain u ⊆ K := by
  apply momentLegendreDomain_subset_of_subgradient_range hLip.continuous hc hK hKc
  exact convexSubgradient_subset_of_momentMap hLip hc hpush hK hKc
    (ae_restrict_mem hK.measurableSet)

theorem moment_convexSubgradient_subsingleton_closedTarget
    {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : Continuous V)
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    (x : Space n) : (convexSubgradient u x).Subsingleton := by
  have hstrict := moment_strictConvexOn hLip hc hV hK.measurableSet hKc hpush
  let M : ℝ := ‖x‖ + 1
  have hxM : ‖x‖ < M := by dsimp [M]; linarith
  have hM : 0 ≤ M := (norm_nonneg x).trans hxM.le
  let f : Space n → ℝ := centeredTruncatedConjugate u x M
  let U : Set (Space n) := truncatedConjugateAgreementRegion u M
  have hU : IsOpen U := isOpen_truncatedConjugateAgreementRegion hLip.continuous hstrict M
  have hcontacts : convexSubgradient u x ⊆ U :=
    convexSubgradient_subset_truncatedConjugateAgreementRegion hLip.continuous hstrict hxM
      (moment_convexSubgradient_subset_interior_domain hLip hc hV hK.measurableSet hKc hpush x)
  have hzeros : {p | f p = 0} ⊆ U := by
    intro p hp
    exact hcontacts ((centeredTruncatedConjugate_eq_zero_iff hLip.continuous hc hxM).mp hp)
  obtain ⟨c, C, hcpos, hcone⟩ :=
    exists_linear_lower_bound_centeredTruncatedConjugate hLip.continuous hxM
  obtain ⟨R, hR, hQ, hQU⟩ := exists_pos_compact_sublevel_subset
    (continuous_centeredTruncatedConjugate hLip.continuous x hM)
    (centeredTruncatedConjugate_nonneg hLip.continuous hxM.le) hcpos hcone hU hzeros
  have hQD : {p | f p ≤ R} ⊆ interior (momentLegendreDomain u) :=
    fun p hp => (hQU hp).1
  have hQK : {p | f p ≤ R} ⊆ K :=
    hQD.trans (interior_subset.trans (momentLegendreDomain_subset_closedTarget hLip hc hK hKc hpush))
  obtain ⟨a, b, ha, hatop, hb, hbtop, hbounds⟩ :=
    exists_local_relativeSubgradientImage_volume_bounds hLip hstrict hV hK.measurableSet
      hpush hQ hQD hQK
  apply convexSubgradient_subsingleton_of_truncated_volume_bounds hLip.continuous hc
    hxM hR ha hatop hb hbtop
  intro S hS hSQ
  rw [volume_convexSubgradientImage_centeredTruncatedConjugate hLip.continuous hstrict x
    (hSQ.trans hQU)]
  exact hbounds S hS hSQ

/-- This conclusion is the actual Fréchet C1 regularity of the original weak
moment potential, derived from its weak transport equation. -/
theorem moment_contDiff_one_closedTarget
    {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : Continuous V)
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K) :
    ContDiff ℝ 1 u := by
  exact contDiff_one_of_subsingleton_convexSubgradient hLip hc
    (moment_convexSubgradient_subsingleton_closedTarget hLip hc hV hK hKc hpush)

end KLS
end

#print axioms KLS.momentLegendreDomain_subset_closedTarget
#print axioms KLS.moment_convexSubgradient_subsingleton_closedTarget
#print axioms KLS.moment_contDiff_one_closedTarget

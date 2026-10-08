import KLS.ReciprocalAlexandrovBounds

/-! The actual positive source density makes its transported measure nonzero.
Absolute continuity of the target then forces a nonempty interior of the
finite conjugate domain. No additional probability normalization is needed. -/

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology NNReal ENNReal

noncomputable section
namespace KLS

variable {n : ℕ}

theorem potentialMeasure_ne_zero_of_measurable
    {u : Space n → ℝ} (hu : Measurable u) : potentialMeasure u ≠ 0 := by
  intro hzero
  have hh := volume_absolutelyContinuous_potentialMeasure_of_measurable hu
  rw [hzero] at hh
  have hvzero := Measure.absolutelyContinuous_zero_iff.mp hh
  exact (NeZero.ne (volume : Measure (Space n))) hvzero

theorem interior_momentLegendreDomain_nonempty_of_ac_target
    {u : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u)
    (htarget : (potentialMeasure u).map (gradient u) ≪ volume) :
    (interior (momentLegendreDomain u)).Nonempty := by
  have hne := potentialMeasure_ne_zero_of_measurable hLip.continuous.measurable
  let : NeZero ((potentialMeasure u).map (gradient u)) :=
    ⟨(Measure.map_ne_zero_iff (measurable_gradient u).aemeasurable).mpr hne⟩
  have hmem := ae_mem_momentLegendreDomain_of_momentMap hLip hc
    (rfl : (potentialMeasure u).map (gradient u) = (potentialMeasure u).map (gradient u))
  have hgood := convexOn_ae_mem_interior_and_differentiableAt htarget
    (convexOn_normalizedLegendreTransform_toReal u) hmem
  obtain ⟨p, hp, _⟩ := hgood.exists
  exact ⟨p, hp⟩

theorem moment_convexSubgradient_subset_interior_domain
    {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : Continuous V)
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    (x : Space n) : convexSubgradient u x ⊆ interior (momentLegendreDomain u) := by
  have htarget : (potentialMeasure u).map (gradient u) ≪ volume := by
    change MomentMap.gradientPushforward u ≪ volume
    rw [hpush]
    exact Measure.restrict_le_self.absolutelyContinuous.trans (withDensity_absolutelyContinuous _ _)
  exact convexSubgradient_subset_interior_momentLegendreDomain hLip.continuous
    (moment_strictConvexOn hLip hc hV hK hKc hpush)
    (interior_momentLegendreDomain_nonempty_of_ac_target hLip hc htarget) x

/-- The actual conjugate gradient transports the actual target back to its
source potential measure. -/
theorem moment_map_gradient_finiteLegendrePotential_inverse
    {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : Continuous V)
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K) :
    ((potentialMeasure V).restrict K).map (gradient (finiteLegendrePotential u)) =
      potentialMeasure u := by
  have htarget : (potentialMeasure u).map (gradient u) ≪ volume := by
    change MomentMap.gradientPushforward u ≪ volume
    rw [hpush]
    exact Measure.restrict_le_self.absolutelyContinuous.trans (withDensity_absolutelyContinuous _ _)
  exact map_gradient_finiteLegendrePotential_inverse hLip
    (moment_strictConvexOn hLip hc hV hK hKc hpush)
    (interior_momentLegendreDomain_nonempty_of_ac_target hLip hc htarget)
    (withDensity_absolutelyContinuous _ _) hpush

end KLS
end

#print axioms KLS.interior_momentLegendreDomain_nonempty_of_ac_target
#print axioms KLS.moment_convexSubgradient_subset_interior_domain
#print axioms KLS.moment_map_gradient_finiteLegendrePotential_inverse

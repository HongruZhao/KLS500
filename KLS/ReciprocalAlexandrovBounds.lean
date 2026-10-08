import KLS.ReciprocalConjugateTransport
import KLS.MomentStrictConvexity

/-!
# Reciprocal Alexandrov equation and local density bounds

On the actual finite conjugate interior, the relative subgradient image has
Lebesgue volume equal to the integral of exp(-V + u composed with the inverse
gradient). This follows from the genuine weak moment transport and its
weighted inverse identity. Positive finite bounds are constructed on each
compact interior region.
-/

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology NNReal ENNReal

noncomputable section
namespace KLS

variable {n : ℕ}

def conjugateMongeAmpereDensity (u V : Space n → ℝ) (p : Space n) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-V p + u (gradient (finiteLegendrePotential u) p)))

def conjugateMongeAmpereMeasure (u V : Space n → ℝ) : Measure (Space n) :=
  volume.withDensity (conjugateMongeAmpereDensity u V)

theorem potentialMeasure_withDensity_exp_inverseGradient
    {u V : Space n → ℝ} (hu : Measurable u) (hV : Measurable V) :
    (potentialMeasure V).withDensity
      (fun p => ENNReal.ofReal (Real.exp (u (gradient (finiteLegendrePotential u) p)))) =
      conjugateMongeAmpereMeasure u V := by
  rw [potentialMeasure, ← withDensity_mul volume
    (f := fun p => ENNReal.ofReal (Real.exp (-V p)))
    (g := fun p => ENNReal.ofReal (Real.exp (u (gradient (finiteLegendrePotential u) p))))
    hV.neg.exp.ennreal_ofReal ((hu.comp (measurable_gradient _)).exp.ennreal_ofReal)]
  congr 1
  funext p
  simp only [Pi.mul_apply, conjugateMongeAmpereDensity,
    ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]

/-- The reciprocal equation concerns relative subgradients on the true
finite domain, never global subgradients of the totalized real function. -/
theorem conjugateMongeAmpereMeasure_apply_eq_relativeSubgradientImage_volume
    {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : StrictConvexOn ℝ univ u) (hV : Measurable V)
    {K : Set (Space n)} (hK : MeasurableSet K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    {S : Set (Space n)} (hS : IsSigmaCompact S)
    (hSD : S ⊆ interior (momentLegendreDomain u)) (hSK : S ⊆ K) :
    conjugateMongeAmpereMeasure u V S =
      volume (convexSubgradientImageOn (finiteLegendrePotential u) (momentLegendreDomain u) S) := by
  have hSm := measurableSet_of_isSigmaCompact_space hS
  have hA := measurableSet_of_isSigmaCompact_space
    (isSigmaCompact_gradient_finiteLegendrePotential_image hLip.continuous hc hS hSD)
  have hρ : potentialMeasure u ≪ volume := withDensity_absolutelyContinuous _ _
  have hh := setLIntegral_comp_gradient_finiteLegendrePotential_eq_image hLip hc
    hρ hSm hA hSD hLip.continuous.measurable.exp.ennreal_ofReal
  change (∫⁻ p in S, ENNReal.ofReal (Real.exp (u (gradient (finiteLegendrePotential u) p)))
    ∂MomentMap.gradientPushforward u) =
      ∫⁻ x in gradient (finiteLegendrePotential u) '' S, ENNReal.ofReal (Real.exp (u x))
        ∂potentialMeasure u at hh
  rw [hpush] at hh
  have hcancel : (potentialMeasure u).withDensity (fun x => ENNReal.ofReal (Real.exp (u x))) =
      volume := by
    simpa only [Measure.restrict_univ] using
      restrict_potentialMeasure_withDensity_exp (V := u) (K := univ)
        hLip.continuous.measurable MeasurableSet.univ
  rw [← withDensity_apply _ hSm, ← restrict_withDensity hK,
    potentialMeasure_withDensity_exp_inverseGradient hLip.continuous.measurable hV,
    Measure.restrict_apply hSm, inter_eq_self_of_subset_left hSK,
    ← withDensity_apply _ hA, hcancel] at hh
  rw [convexSubgradientImageOn_finiteLegendrePotential_eq_gradient_image hLip.continuous hc hSD]
  exact hh

theorem exists_local_conjugateMongeAmpereDensity_bounds
    {u V : Space n → ℝ} (hu : Continuous u) (hc : StrictConvexOn ℝ univ u)
    (hV : Continuous V) {Q : Set (Space n)} (hQ : IsCompact Q)
    (hQD : Q ⊆ interior (momentLegendreDomain u)) :
    ∃ a b : ℝ≥0∞, 0 < a ∧ a < ∞ ∧ 0 < b ∧ b < ∞ ∧
      ∀ p ∈ Q, a ≤ conjugateMongeAmpereDensity u V p ∧
        conjugateMongeAmpereDensity u V p ≤ b := by
  have hg : ContinuousOn (gradient (finiteLegendrePotential u)) Q :=
    (continuousOn_gradient_finiteLegendrePotential_of_strictConvexOn hu hc).mono hQD
  have hF : ContinuousOn (fun p => -V p + u (gradient (finiteLegendrePotential u) p)) Q :=
    hV.continuousOn.neg.add (hu.comp_continuousOn hg)
  obtain ⟨m, hm⟩ := hQ.bddBelow_image hF
  obtain ⟨M, hM⟩ := hQ.bddAbove_image hF
  refine ⟨ENNReal.ofReal (Real.exp m), ENNReal.ofReal (Real.exp M),
    ENNReal.ofReal_pos.mpr (Real.exp_pos _), ENNReal.ofReal_lt_top,
    ENNReal.ofReal_pos.mpr (Real.exp_pos _), ENNReal.ofReal_lt_top, ?_⟩
  intro p hp
  constructor <;> apply ENNReal.ofReal_le_ofReal <;> apply Real.exp_le_exp.mpr
  · exact hm (mem_image_of_mem _ hp)
  · exact hM (mem_image_of_mem _ hp)

/-- The actual inverse equation supplies uniform positive finite Alexandrov
bounds for every sigma-compact subset of a fixed compact interior region. -/
theorem exists_local_relativeSubgradientImage_volume_bounds
    {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : StrictConvexOn ℝ univ u) (hV : Continuous V)
    {K : Set (Space n)} (hK : MeasurableSet K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    {Q : Set (Space n)} (hQ : IsCompact Q)
    (hQD : Q ⊆ interior (momentLegendreDomain u)) (hQK : Q ⊆ K) :
    ∃ a b : ℝ≥0∞, 0 < a ∧ a < ∞ ∧ 0 < b ∧ b < ∞ ∧
      ∀ S : Set (Space n), IsSigmaCompact S → S ⊆ Q →
        a * volume S ≤ volume (convexSubgradientImageOn (finiteLegendrePotential u)
          (momentLegendreDomain u) S) ∧
        volume (convexSubgradientImageOn (finiteLegendrePotential u)
          (momentLegendreDomain u) S) ≤ b * volume S := by
  obtain ⟨a, b, ha, hatop, hb, hbtop, hbound⟩ :=
    exists_local_conjugateMongeAmpereDensity_bounds hLip.continuous hc hV hQ hQD
  refine ⟨a, b, ha, hatop, hb, hbtop, ?_⟩
  intro S hS hSQ
  have hSm := measurableSet_of_isSigmaCompact_space hS
  rw [← conjugateMongeAmpereMeasure_apply_eq_relativeSubgradientImage_volume hLip hc
    hV.measurable hK hpush hS (hSQ.trans hQD) (hSQ.trans hQK)]
  rw [conjugateMongeAmpereMeasure, withDensity_apply _ hSm]
  constructor
  · calc
      _ = ∫⁻ _p in S, a ∂volume := by simp
      _ ≤ _ := setLIntegral_mono' hSm (fun p hp => (hbound p (hSQ hp)).1)
  · calc
      _ ≤ ∫⁻ _p in S, b ∂volume := setLIntegral_mono' hSm (fun p hp => (hbound p (hSQ hp)).2)
      _ = _ := by simp

/-- The primal strict-convexity theorem discharges that hypothesis for the
actual weak moment potential. -/
theorem exists_local_moment_conjugate_volume_bounds
    {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : Continuous V)
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    {Q : Set (Space n)} (hQ : IsCompact Q)
    (hQD : Q ⊆ interior (momentLegendreDomain u)) (hQK : Q ⊆ K) :
    ∃ a b : ℝ≥0∞, 0 < a ∧ a < ∞ ∧ 0 < b ∧ b < ∞ ∧
      ∀ S : Set (Space n), IsSigmaCompact S → S ⊆ Q →
        a * volume S ≤ volume (convexSubgradientImageOn (finiteLegendrePotential u)
          (momentLegendreDomain u) S) ∧
        volume (convexSubgradientImageOn (finiteLegendrePotential u)
          (momentLegendreDomain u) S) ≤ b * volume S :=
  exists_local_relativeSubgradientImage_volume_bounds hLip
    (moment_strictConvexOn hLip hc hV hK hKc hpush) hV hK hpush hQ hQD hQK

end KLS
end

#print axioms KLS.conjugateMongeAmpereMeasure_apply_eq_relativeSubgradientImage_volume
#print axioms KLS.exists_local_relativeSubgradientImage_volume_bounds
#print axioms KLS.exists_local_moment_conjugate_volume_bounds

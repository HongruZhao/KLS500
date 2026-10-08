import KLS.WeakSubgradientTransport
import KLS.SubgradientLocalMass
import KLS.MomentGradientRange

/-! Two-sided local volume bounds for actual subgradient images of a weak
moment-map potential. The density, weak transport, global support range and
inverse uniqueness all refer to actual functions and measures. No strict
convexity, classical Hessian, or PDE regularity is among the hypotheses. -/

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology NNReal ENNReal

noncomputable section
namespace KLS

variable {n : ℕ}

theorem exists_restrict_volume_closure_le_smul_restrict_potentialMeasure
    {V : Space n → ℝ} (hV : Continuous V) {K : Set (Space n)}
    (hK : MeasurableSet K) (hc : Convex ℝ K) (hb : Bornology.IsBounded K) :
    ∃ D : ℝ≥0∞, 0 < D ∧ D < ∞ ∧
      volume.restrict (closure K) ≤ D • (potentialMeasure V).restrict K := by
  obtain ⟨M, hM⟩ := hb.isCompact_closure.bddAbove_image hV.continuousOn
  refine ⟨ENNReal.ofReal (Real.exp M), ENNReal.ofReal_pos.mpr (Real.exp_pos _),
    ENNReal.ofReal_lt_top, ?_⟩
  have hvol : volume.restrict (closure K) = volume.restrict K :=
    Measure.restrict_congr_set (closure_ae_eq_of_null_frontier (hc.addHaar_frontier volume))
  rw [hvol]
  have hh := Measure.restrict_mono_measure
    (restrict_volume_le_exp_smul_potentialMeasure hV.measurable hK
      (fun x hx => hM (mem_image_of_mem V (subset_closure hx)))) K
  simpa only [Measure.restrict_restrict hK, inter_self, Measure.restrict_smul] using hh

theorem subgradientImage_subset_closure_of_weak_momentMap
    {φ V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L φ)
    (hc : ConvexOn ℝ univ φ) {K : Set (Space n)} (hK : MeasurableSet K)
    (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward φ = (potentialMeasure V).restrict K)
    (S : Set (Space n)) : convexSubgradientImage φ S ⊆ closure K := by
  have htarget : ∀ᵐ p ∂(potentialMeasure V).restrict K, p ∈ closure K :=
    (ae_restrict_mem hK).mono (fun _ hp => subset_closure hp)
  have hr := convexSubgradient_subset_of_momentMap hLip hc hpush
    isClosed_closure hKc.closure htarget
  rintro p ⟨x, _, hp⟩
  exact hr x hp

/-- Exact weighted Alexandrov identity for each compact source set. -/
theorem potentialMeasure_eq_target_subgradientImage_of_weak_momentMap
    {φ V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L φ)
    (hc : ConvexOn ℝ univ φ) {K : Set (Space n)}
    (hpush : MomentMap.gradientPushforward φ = (potentialMeasure V).restrict K)
    {S : Set (Space n)} (hS : IsCompact S) :
    potentialMeasure φ S = (potentialMeasure V).restrict K (convexSubgradientImage φ S) := by
  have hρ : potentialMeasure φ ≪ volume := withDensity_absolutelyContinuous _ _
  have htarget : (potentialMeasure φ).map (gradient φ) ≪ volume := by
    change MomentMap.gradientPushforward φ ≪ volume
    rw [hpush]
    exact Measure.restrict_le_self.absolutelyContinuous.trans (withDensity_absolutelyContinuous _ _)
  have hh := measure_eq_map_gradient_convexSubgradientImage hLip hc hρ htarget hS
  change potentialMeasure φ S = MomentMap.gradientPushforward φ _ at hh
  simpa only [hpush] using hh

/-- The volume of every compact subgradient image is bounded above and below
by finite positive multiples of source volume, locally in the source. The
constants are constructed from compact density bounds. -/
theorem exists_local_subgradient_volume_two_sided_bounds
    {φ V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L φ)
    (hc : ConvexOn ℝ univ φ) (hV : Continuous V)
    {K : Set (Space n)} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hb : Bornology.IsBounded K)
    (hpush : MomentMap.gradientPushforward φ = (potentialMeasure V).restrict K)
    {Q : Set (Space n)} (hQ : IsCompact Q) :
    ∃ c C : ℝ≥0∞, 0 < c ∧ c < ∞ ∧ 0 < C ∧ C < ∞ ∧
      ∀ S : Set (Space n), IsCompact S → S ⊆ Q →
        volume S ≤ c * volume (convexSubgradientImage φ S) ∧
        volume (convexSubgradientImage φ S) ≤ C * volume S := by
  obtain ⟨c, hcpos, hcfin, hclower⟩ :=
    exists_local_subgradient_volume_lower_bound hLip hc hV hK hb hpush hQ
  obtain ⟨D, hDpos, hDfin, hD⟩ :=
    exists_restrict_volume_closure_le_smul_restrict_potentialMeasure hV hK hKc hb
  obtain ⟨m, hm⟩ := hQ.bddBelow_image hLip.continuous.continuousOn
  let B : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-m))
  have hBpos : 0 < B := ENNReal.ofReal_pos.mpr (Real.exp_pos _)
  have hBfin : B < ∞ := ENNReal.ofReal_lt_top
  have hB := restrict_potentialMeasure_le_exp_smul_volume hQ.measurableSet
    (fun x hx => hm (mem_image_of_mem φ hx))
  refine ⟨c, D * B, hcpos, hcfin, by positivity,
    ENNReal.mul_lt_top hDfin hBfin, ?_⟩
  intro S hS hSQ
  refine ⟨hclower S hS hSQ, ?_⟩
  have hAsub := subgradientImage_subset_closure_of_weak_momentMap hLip hc hK hKc hpush S
  have himage := hD (convexSubgradientImage φ S)
  rw [Measure.restrict_apply (isCompact_convexSubgradientImage hLip hS).measurableSet,
    inter_eq_self_of_subset_left hAsub, Measure.smul_apply, smul_eq_mul,
    ← potentialMeasure_eq_target_subgradientImage_of_weak_momentMap hLip hc hpush hS] at himage
  have hsource := hB S
  rw [Measure.restrict_apply hS.measurableSet, inter_eq_self_of_subset_left hSQ,
    Measure.smul_apply, smul_eq_mul] at hsource
  calc
    volume (convexSubgradientImage φ S) ≤ D * potentialMeasure φ S := himage
    _ ≤ D * (B * volume S) := mul_le_mul_right hsource D
    _ = (D * B) * volume S := (mul_assoc _ _ _).symm

end KLS
end

#print axioms KLS.potentialMeasure_eq_target_subgradientImage_of_weak_momentMap
#print axioms KLS.exists_local_subgradient_volume_two_sided_bounds

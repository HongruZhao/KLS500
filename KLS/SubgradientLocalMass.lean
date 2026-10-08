import KLS.SubgradientTransport
import KLS.WeightedLocalDistribution

/-! Actual local lower bounds for subgradient-image volume obtained from
weak gradient transport to a bounded positive continuous density. These are
measure inequalities for the explicitly defined subgradient image, not an
assumed Alexandrov-solution or regularity certificate. -/

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology NNReal ENNReal

noncomputable section
namespace KLS

variable {n : ℕ}

theorem restrict_potentialMeasure_le_exp_smul_volume {V : Space n → ℝ}
    {K : Set (Space n)} (hK : MeasurableSet K) {m : ℝ}
    (hm : ∀ y ∈ K, m ≤ V y) :
    (potentialMeasure V).restrict K ≤ ENNReal.ofReal (Real.exp (-m)) • volume := by
  rw [potentialMeasure, restrict_withDensity hK, ← withDensity_indicator hK,
    ← withDensity_const]
  apply withDensity_mono
  apply Eventually.of_forall
  intro y
  by_cases hy : y ∈ K
  · simp only [indicator_of_mem hy]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg (hm y hy)))
  · simp only [indicator_of_notMem hy]
    exact zero_le

theorem exists_restrict_potentialMeasure_le_smul_volume {V : Space n → ℝ}
    (hV : Continuous V) {K : Set (Space n)} (hK : MeasurableSet K)
    (hb : Bornology.IsBounded K) :
    ∃ D : ℝ≥0∞, 0 < D ∧ D < ∞ ∧ (potentialMeasure V).restrict K ≤ D • volume := by
  obtain ⟨m, hm⟩ := hb.isCompact_closure.bddBelow_image hV.continuousOn
  refine ⟨ENNReal.ofReal (Real.exp (-m)), ENNReal.ofReal_pos.mpr (Real.exp_pos _),
    ENNReal.ofReal_lt_top, restrict_potentialMeasure_le_exp_smul_volume hK ?_⟩
  intro y hy
  exact hm (mem_image_of_mem V (subset_closure hy))

/-- Every compact source region has a finite positive local lower-volume
constant, derived from the actual weak transport and actual target density. -/
theorem exists_local_subgradient_volume_lower_bound
    {φ V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L φ)
    (hc : ConvexOn ℝ univ φ) (hV : Continuous V)
    {K : Set (Space n)} (hK : MeasurableSet K) (hb : Bornology.IsBounded K)
    (hpush : MomentMap.gradientPushforward φ = (potentialMeasure V).restrict K)
    {Q : Set (Space n)} (hQ : IsCompact Q) :
    ∃ C : ℝ≥0∞, 0 < C ∧ C < ∞ ∧
      ∀ S : Set (Space n), IsCompact S → S ⊆ Q →
        volume S ≤ C * volume (convexSubgradientImage φ S) := by
  obtain ⟨D, hDpos, hDfinite, hD⟩ :=
    exists_restrict_potentialMeasure_le_smul_volume hV hK hb
  obtain ⟨M, hM⟩ := hQ.bddAbove_image hLip.continuous.continuousOn
  let A : ℝ≥0∞ := ENNReal.ofReal (Real.exp M)
  have hApos : 0 < A := ENNReal.ofReal_pos.mpr (Real.exp_pos _)
  have hAfin : A < ∞ := ENNReal.ofReal_lt_top
  have hA := restrict_volume_le_exp_smul_potentialMeasure hLip.continuous.measurable
    hQ.measurableSet (fun x hx => hM (mem_image_of_mem φ hx))
  refine ⟨A * D, by positivity, ENNReal.mul_lt_top hAfin hDfinite, ?_⟩
  intro S hS hSQ
  have hsrc := hA S
  rw [Measure.restrict_apply hS.measurableSet, inter_eq_self_of_subset_left hSQ,
    Measure.smul_apply, smul_eq_mul] at hsrc
  have htransport := potentialMeasure_le_gradientPushforward_convexSubgradientImage hLip hc hS
  rw [hpush] at htransport
  have htgt := hD (convexSubgradientImage φ S)
  rw [Measure.smul_apply, smul_eq_mul] at htgt
  calc
    volume S ≤ A * potentialMeasure φ S := hsrc
    _ ≤ A * (D * volume (convexSubgradientImage φ S)) :=
      mul_le_mul_right (htransport.trans htgt) A
    _ = (A * D) * volume (convexSubgradientImage φ S) := (mul_assoc _ _ _).symm

end KLS
end

#print axioms KLS.exists_restrict_potentialMeasure_le_smul_volume
#print axioms KLS.exists_local_subgradient_volume_lower_bound

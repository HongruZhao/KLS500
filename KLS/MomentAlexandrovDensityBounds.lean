import KLS.MomentAlexandrovOpen

/-!
# Local bounds for the actual weak Monge--Ampere density

The global Lipschitz bound controls the gradient even at nondifferentiability
points, where its totalized value is zero. Compact bounds on the source
potential and on the target potential over the gradient ball therefore give
positive finite pointwise density bounds. The actual Alexandrov identity
then transfers these bounds to all sigma-compact source sets in that region.
-/

open MeasureTheory InnerProductSpace Set Metric
open scoped Topology NNReal ENNReal

noncomputable section
namespace KLS

variable {n : ℕ}

theorem norm_gradient_le_of_lipschitz
    {φ : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L φ) (x : Space n) :
    ‖gradient φ x‖ ≤ L := by
  rw [norm_gradient_eq_norm_fderiv]
  exact norm_fderiv_le_of_lipschitz ℝ hLip

/-- Constructed, pointwise, positive finite bounds; differentiability of the
source potential is not assumed. -/
theorem exists_local_momentMongeAmpereDensity_bounds
    {φ V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L φ)
    (hV : Continuous V) {Q : Set (Space n)} (hQ : IsCompact Q) :
    ∃ a b : ℝ≥0∞, 0 < a ∧ a < ∞ ∧ 0 < b ∧ b < ∞ ∧
      ∀ x ∈ Q, a ≤ momentMongeAmpereDensity φ V x ∧
        momentMongeAmpereDensity φ V x ≤ b := by
  obtain ⟨φlo, hφlo⟩ := hQ.bddBelow_image hLip.continuous.continuousOn
  obtain ⟨φhi, hφhi⟩ := hQ.bddAbove_image hLip.continuous.continuousOn
  obtain ⟨Vlo, hVlo⟩ := (isCompact_closedBall (0 : Space n) (L : ℝ)).bddBelow_image
    hV.continuousOn
  obtain ⟨Vhi, hVhi⟩ := (isCompact_closedBall (0 : Space n) (L : ℝ)).bddAbove_image
    hV.continuousOn
  refine ⟨ENNReal.ofReal (Real.exp (-φhi + Vlo)),
    ENNReal.ofReal (Real.exp (-φlo + Vhi)),
    ENNReal.ofReal_pos.mpr (Real.exp_pos _), ENNReal.ofReal_lt_top,
    ENNReal.ofReal_pos.mpr (Real.exp_pos _), ENNReal.ofReal_lt_top, ?_⟩
  intro x hx
  have hφlower := hφlo (mem_image_of_mem φ hx)
  have hφupper := hφhi (mem_image_of_mem φ hx)
  have hgrad : gradient φ x ∈ closedBall 0 (L : ℝ) := by
    simpa only [mem_closedBall, dist_zero_right] using norm_gradient_le_of_lipschitz hLip x
  have hVlower := hVlo (mem_image_of_mem V hgrad)
  have hVupper := hVhi (mem_image_of_mem V hgrad)
  constructor <;> apply ENNReal.ofReal_le_ofReal <;> apply Real.exp_le_exp.mpr <;> linarith

/-- Pointwise density bounds imply bounds for the measure of every
measurable set in the region. -/
theorem momentMongeAmpereMeasure_apply_bounds_of_density
    {φ V : Space n → ℝ} {Q S : Set (Space n)} {a b : ℝ≥0∞}
    (hS : MeasurableSet S) (hSQ : S ⊆ Q)
    (hbound : ∀ x ∈ Q, a ≤ momentMongeAmpereDensity φ V x ∧
      momentMongeAmpereDensity φ V x ≤ b) :
    a * volume S ≤ momentMongeAmpereMeasure φ V S ∧
      momentMongeAmpereMeasure φ V S ≤ b * volume S := by
  rw [momentMongeAmpereMeasure, withDensity_apply _ hS]
  constructor
  · calc
      _ = ∫⁻ _x in S, a ∂volume := by simp
      _ ≤ _ := setLIntegral_mono' hS (fun x hx => (hbound x (hSQ hx)).1)
  · calc
      _ ≤ ∫⁻ _x in S, b ∂volume :=
        setLIntegral_mono' hS (fun x hx => (hbound x (hSQ hx)).2)
      _ = _ := by simp

/-- Every sigma-compact source set in a fixed compact region satisfies
two-sided bounds for its actual subgradient-image volume. The constants
are constructed from the given potentials. -/
theorem exists_local_subgradient_volume_bounds_sigmaCompact
    {φ V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L φ)
    (hc : ConvexOn ℝ univ φ) (hV : Continuous V)
    {K : Set (Space n)} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward φ = (potentialMeasure V).restrict K)
    {Q : Set (Space n)} (hQ : IsCompact Q) :
    ∃ a b : ℝ≥0∞, 0 < a ∧ a < ∞ ∧ 0 < b ∧ b < ∞ ∧
      ∀ S : Set (Space n), IsSigmaCompact S → S ⊆ Q →
        a * volume S ≤ volume (convexSubgradientImage φ S) ∧
        volume (convexSubgradientImage φ S) ≤ b * volume S := by
  obtain ⟨a, b, ha, hatop, hb, hbtop, hbounds⟩ :=
    exists_local_momentMongeAmpereDensity_bounds hLip hV hQ
  refine ⟨a, b, ha, hatop, hb, hbtop, ?_⟩
  intro S hS hSQ
  rw [← momentMongeAmpereMeasure_apply_eq_subgradientImage_volume_of_sigmaCompact
    hLip hc hV.measurable hK hKc hpush hS]
  exact momentMongeAmpereMeasure_apply_bounds_of_density
    (measurableSet_of_isSigmaCompact_space hS) hSQ hbounds

/-- In particular the same constants control every open source section
contained in the chosen compact region. -/
theorem exists_local_subgradient_volume_bounds_open
    {φ V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L φ)
    (hc : ConvexOn ℝ univ φ) (hV : Continuous V)
    {K : Set (Space n)} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward φ = (potentialMeasure V).restrict K)
    {Q : Set (Space n)} (hQ : IsCompact Q) :
    ∃ a b : ℝ≥0∞, 0 < a ∧ a < ∞ ∧ 0 < b ∧ b < ∞ ∧
      ∀ S : Set (Space n), IsOpen S → S ⊆ Q →
        a * volume S ≤ volume (convexSubgradientImage φ S) ∧
        volume (convexSubgradientImage φ S) ≤ b * volume S := by
  obtain ⟨a, b, ha, hatop, hb, hbtop, hbounds⟩ :=
    exists_local_subgradient_volume_bounds_sigmaCompact hLip hc hV hK hKc hpush hQ
  exact ⟨a, b, ha, hatop, hb, hbtop,
    fun S hS hSQ => hbounds S (isSigmaCompact_of_isOpen_space hS) hSQ⟩

end KLS
end

#print axioms KLS.norm_gradient_le_of_lipschitz
#print axioms KLS.exists_local_momentMongeAmpereDensity_bounds
#print axioms KLS.momentMongeAmpereMeasure_apply_bounds_of_density
#print axioms KLS.exists_local_subgradient_volume_bounds_sigmaCompact
#print axioms KLS.exists_local_subgradient_volume_bounds_open

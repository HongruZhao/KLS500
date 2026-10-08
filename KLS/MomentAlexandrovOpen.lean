import KLS.MomentAlexandrovEquation
import Mathlib.Topology.Compactness.SigmaCompact

/-! The weak Monge--Ampere equation on open sections.  The subgradient image
of a sigma-compact set is sigma-compact for the actual Lipschitz potential.
Consequently no measurability hypothesis on such an image is needed. -/

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology NNReal ENNReal

noncomputable section
namespace KLS

variable {n : ℕ}

theorem convexSubgradientImage_iUnion (φ : Space n → ℝ) (S : ℕ → Set (Space n)) :
    convexSubgradientImage φ (⋃ k, S k) = ⋃ k, convexSubgradientImage φ (S k) := by
  ext p
  simp only [convexSubgradientImage, mem_ofPred, mem_iUnion]
  aesop

theorem isSigmaCompact_convexSubgradientImage {φ : Space n → ℝ} {L : ℝ≥0}
    (hLip : LipschitzWith L φ) {S : Set (Space n)} (hS : IsSigmaCompact S) :
    IsSigmaCompact (convexSubgradientImage φ S) := by
  obtain ⟨Q, hQ, heq⟩ := hS
  rw [← heq, convexSubgradientImage_iUnion]
  exact isSigmaCompact_iUnion_of_isCompact _ (fun k => isCompact_convexSubgradientImage hLip (hQ k))

theorem measurableSet_of_isSigmaCompact_space {S : Set (Space n)}
    (hS : IsSigmaCompact S) : MeasurableSet S := by
  obtain ⟨Q, hQ, heq⟩ := hS
  rw [← heq]
  exact MeasurableSet.iUnion (fun k => (hQ k).measurableSet)

theorem isSigmaCompact_of_isOpen_space {S : Set (Space n)} (hS : IsOpen S) :
    IsSigmaCompact S := by
  let : LocallyCompactSpace S := hS.locallyCompactSpace
  exact isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance

theorem setLIntegral_comp_gradient_eq_subgradientImage_of_measurable
    {φ : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L φ)
    (hc : ConvexOn ℝ univ φ) {ρ : Measure (Space n)} (hρ : ρ ≪ volume)
    (htarget : ρ.map (gradient φ) ≪ volume) {S : Set (Space n)}
    (hS : MeasurableSet S) (hA : MeasurableSet (convexSubgradientImage φ S))
    {w : Space n → ℝ≥0∞} (hw : Measurable w) :
    ∫⁻ x in S, w (gradient φ x) ∂ρ =
      ∫⁻ p in convexSubgradientImage φ S, w p ∂ρ.map (gradient φ) := by
  rw [← lintegral_indicator hS, ← lintegral_indicator hA,
    lintegral_map (hw.indicator hA) (measurable_gradient φ)]
  apply lintegral_congr_ae
  filter_upwards [preimage_convexSubgradientImage_ae_eq hLip hc hρ htarget S] with x hx
  by_cases hxs : x ∈ S
  · have hxa : gradient φ x ∈ convexSubgradientImage φ S := by
      change x ∈ gradient φ ⁻¹' convexSubgradientImage φ S
      rw [hx]
      exact hxs
    simp only [indicator_of_mem hxs, indicator_of_mem hxa]
  · have hxa : gradient φ x ∉ convexSubgradientImage φ S := by
      change x ∉ gradient φ ⁻¹' convexSubgradientImage φ S
      rw [hx]
      exact hxs
    simp only [indicator_of_notMem hxs, indicator_of_notMem hxa]

theorem momentMongeAmpereMeasure_apply_eq_subgradientImage_volume_of_sigmaCompact
    {φ V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L φ)
    (hc : ConvexOn ℝ univ φ) (hV : Measurable V)
    {K : Set (Space n)} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward φ = (potentialMeasure V).restrict K)
    {S : Set (Space n)} (hS : IsSigmaCompact S) :
    momentMongeAmpereMeasure φ V S = volume (convexSubgradientImage φ S) := by
  have hSm := measurableSet_of_isSigmaCompact_space hS
  have hA := measurableSet_of_isSigmaCompact_space (isSigmaCompact_convexSubgradientImage hLip hS)
  have hρ : potentialMeasure φ ≪ volume := withDensity_absolutelyContinuous _ _
  have htarget : (potentialMeasure φ).map (gradient φ) ≪ volume := by
    change MomentMap.gradientPushforward φ ≪ volume
    rw [hpush]
    exact Measure.restrict_le_self.absolutelyContinuous.trans (withDensity_absolutelyContinuous _ _)
  have hAsub := subgradientImage_subset_closure_of_weak_momentMap hLip hc hK hKc hpush S
  have hh := setLIntegral_comp_gradient_eq_subgradientImage_of_measurable
    hLip hc hρ htarget hSm hA hV.exp.ennreal_ofReal
  change (∫⁻ x in S, ENNReal.ofReal (Real.exp (V (gradient φ x))) ∂potentialMeasure φ) =
    ∫⁻ p in convexSubgradientImage φ S, ENNReal.ofReal (Real.exp (V p))
      ∂MomentMap.gradientPushforward φ at hh
  rw [hpush] at hh
  rw [← potentialMeasure_withDensity_exp_gradient hLip.continuous.measurable hV,
    withDensity_apply _ hSm, hh,
    ← withDensity_apply _ hA, restrict_potentialMeasure_withDensity_exp hV hK]
  have hvol : volume.restrict K = volume.restrict (closure K) :=
    (Measure.restrict_congr_set
      (closure_ae_eq_of_null_frontier (hKc.addHaar_frontier volume))).symm
  rw [hvol, Measure.restrict_apply hA, inter_eq_self_of_subset_left hAsub]

theorem momentMongeAmpereMeasure_apply_eq_subgradientImage_volume_of_isOpen
    {φ V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L φ)
    (hc : ConvexOn ℝ univ φ) (hV : Measurable V)
    {K : Set (Space n)} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward φ = (potentialMeasure V).restrict K)
    {S : Set (Space n)} (hS : IsOpen S) :
    momentMongeAmpereMeasure φ V S = volume (convexSubgradientImage φ S) :=
  momentMongeAmpereMeasure_apply_eq_subgradientImage_volume_of_sigmaCompact
    hLip hc hV hK hKc hpush (isSigmaCompact_of_isOpen_space hS)

end KLS
end

#print axioms KLS.isSigmaCompact_convexSubgradientImage
#print axioms KLS.momentMongeAmpereMeasure_apply_eq_subgradientImage_volume_of_isOpen

import KLS.ConvexSubgradient
import KLS.MomentMapIntegration

/-! Measure identities and inequalities for actual subgradient images.
The lower bound is obtained directly from an absolutely continuous source
and its genuine gradient pushforward. Equality is proved under ordinary
strict convexity, which is kept explicit rather than treated as established
regularity of a variational optimizer. -/

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology NNReal ENNReal

noncomputable section
namespace KLS

variable {n : ℕ}

theorem measure_le_map_gradient_convexSubgradientImage
    {φ : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L φ)
    (hc : ConvexOn ℝ univ φ) {ρ : Measure (Space n)} (hρ : ρ ≪ volume)
    {S : Set (Space n)} (hS : IsCompact S) :
    ρ S ≤ (ρ.map (gradient φ)) (convexSubgradientImage φ S) := by
  rw [Measure.map_apply (measurable_gradient φ)
    (isCompact_convexSubgradientImage hLip hS).measurableSet]
  apply measure_mono_ae
  filter_upwards [locallyLipschitz_ae_differentiableAt_of_absolutelyContinuous hρ
    hLip.locallyLipschitz] with x hx
  intro hxS
  exact ⟨x, hxS, gradient_mem_convexSubgradient hc hx⟩

theorem eq_of_common_convexSubgradient {φ : Space n → ℝ}
    (hc : StrictConvexOn ℝ univ φ) {x y p : Space n}
    (hp : p ∈ convexSubgradient φ x) (hq : p ∈ convexSubgradient φ y) : x = y := by
  by_contra hxy
  have hh := hc.2 (mem_univ x) (mem_univ y) hxy
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have hy := hp y
  have hx := hq x
  have hm := hp ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y)
  simp only [inner_sub_right, inner_add_right, inner_smul_right, smul_eq_mul] at hy hx hm hh
  linarith

theorem measure_eq_map_gradient_convexSubgradientImage_of_strictConvex
    {φ : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L φ)
    (hc : StrictConvexOn ℝ univ φ) {ρ : Measure (Space n)} (hρ : ρ ≪ volume)
    {S : Set (Space n)} (hS : IsCompact S) :
    ρ S = (ρ.map (gradient φ)) (convexSubgradientImage φ S) := by
  rw [Measure.map_apply (measurable_gradient φ)
    (isCompact_convexSubgradientImage hLip hS).measurableSet]
  apply measure_congr
  filter_upwards [locallyLipschitz_ae_differentiableAt_of_absolutelyContinuous hρ
    hLip.locallyLipschitz] with x hx
  apply propext
  constructor
  · intro hxS
    exact ⟨x, hxS, gradient_mem_convexSubgradient hc.convexOn hx⟩
  · rintro ⟨y, hyS, hxy⟩
    have heq := eq_of_common_convexSubgradient hc
      (gradient_mem_convexSubgradient hc.convexOn hx) hxy
    simpa only [heq] using hyS

theorem potentialMeasure_le_gradientPushforward_convexSubgradientImage
    {φ : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L φ)
    (hc : ConvexOn ℝ univ φ) {S : Set (Space n)} (hS : IsCompact S) :
    potentialMeasure φ S ≤ MomentMap.gradientPushforward φ (convexSubgradientImage φ S) :=
  measure_le_map_gradient_convexSubgradientImage hLip hc
    (withDensity_absolutelyContinuous _ _) hS

end KLS
end

#print axioms KLS.measure_le_map_gradient_convexSubgradientImage
#print axioms KLS.measure_eq_map_gradient_convexSubgradientImage_of_strictConvex

import KLS.MomentAlexandrovBounds

/-! The actual weak Monge--Ampere equation of the constructed moment map.
The source-side measure has explicit density exp(-φ + V ∘ gradient φ).
Its value on each compact set is exactly the Lebesgue volume of that set's
ordinary subgradient image. No determinant or classical differentiability is
used to define the measure or to prove this Alexandrov identity. -/

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology NNReal ENNReal

noncomputable section
namespace KLS

variable {n : ℕ}

theorem preimage_convexSubgradientImage_ae_eq
    {φ : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L φ)
    (hc : ConvexOn ℝ univ φ) {ρ : Measure (Space n)} (hρ : ρ ≪ volume)
    (htarget : ρ.map (gradient φ) ≪ volume) (S : Set (Space n)) :
    (gradient φ ⁻¹' convexSubgradientImage φ S) =ᵐ[ρ] S := by
  have hunique := ae_of_ae_map (measurable_gradient φ).aemeasurable
    (ae_unique_inverse_convexSubgradient hLip hc hρ htarget)
  filter_upwards [locallyLipschitz_ae_differentiableAt_of_absolutelyContinuous hρ
    hLip.locallyLipschitz, hunique] with x hx hu
  apply propext
  constructor
  · rintro ⟨y, hyS, hxy⟩
    have heq := hu x y (gradient_mem_convexSubgradient hc hx) hxy
    simpa only [heq] using hyS
  · intro hxS
    exact ⟨x, hxS, gradient_mem_convexSubgradient hc hx⟩

theorem setLIntegral_comp_gradient_eq_subgradientImage
    {φ : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L φ)
    (hc : ConvexOn ℝ univ φ) {ρ : Measure (Space n)} (hρ : ρ ≪ volume)
    (htarget : ρ.map (gradient φ) ≪ volume) {S : Set (Space n)} (hS : IsCompact S)
    {w : Space n → ℝ≥0∞} (hw : Measurable w) :
    ∫⁻ x in S, w (gradient φ x) ∂ρ =
      ∫⁻ p in convexSubgradientImage φ S, w p ∂ρ.map (gradient φ) := by
  have hA := (isCompact_convexSubgradientImage hLip hS).measurableSet
  rw [← lintegral_indicator hS.measurableSet, ← lintegral_indicator hA,
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

def momentMongeAmpereDensity (φ V : Space n → ℝ) (x : Space n) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-φ x + V (gradient φ x)))

def momentMongeAmpereMeasure (φ V : Space n → ℝ) : Measure (Space n) :=
  volume.withDensity (momentMongeAmpereDensity φ V)

theorem measurable_momentMongeAmpereDensity {φ V : Space n → ℝ}
    (hφ : Measurable φ) (hV : Measurable V) : Measurable (momentMongeAmpereDensity φ V) :=
  (hφ.neg.add (hV.comp (measurable_gradient φ))).exp.ennreal_ofReal

theorem potentialMeasure_withDensity_exp_gradient {φ V : Space n → ℝ}
    (hφ : Measurable φ) (hV : Measurable V) :
    (potentialMeasure φ).withDensity (fun x => ENNReal.ofReal (Real.exp (V (gradient φ x)))) =
      momentMongeAmpereMeasure φ V := by
  rw [potentialMeasure, ← withDensity_mul volume
    (f := fun x => ENNReal.ofReal (Real.exp (-φ x)))
    (g := fun x => ENNReal.ofReal (Real.exp (V (gradient φ x))))
    hφ.neg.exp.ennreal_ofReal ((hV.comp (measurable_gradient φ)).exp.ennreal_ofReal)]
  congr 1
  funext x
  simp only [Pi.mul_apply, momentMongeAmpereDensity,
    ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]

theorem restrict_potentialMeasure_withDensity_exp {V : Space n → ℝ}
    (hV : Measurable V) {K : Set (Space n)} (hK : MeasurableSet K) :
    ((potentialMeasure V).restrict K).withDensity (fun p => ENNReal.ofReal (Real.exp (V p))) =
      volume.restrict K := by
  rw [potentialMeasure, restrict_withDensity hK,
    ← withDensity_mul (volume.restrict K)
      (f := fun x => ENNReal.ofReal (Real.exp (-V x)))
      (g := fun x => ENNReal.ofReal (Real.exp (V x)))
      hV.neg.exp.ennreal_ofReal hV.exp.ennreal_ofReal]
  have heq : (fun p => ENNReal.ofReal (Real.exp (-V p))) *
      (fun p => ENNReal.ofReal (Real.exp (V p))) = 1 := by
    funext p
    simp only [Pi.mul_apply, Pi.one_apply, ← ENNReal.ofReal_mul (Real.exp_nonneg _),
      ← Real.exp_add, neg_add_cancel, Real.exp_zero, ENNReal.ofReal_one]
  rw [heq, withDensity_one]

/-- An actual Alexandrov equation: the explicitly given source density
integrates to the volume of the ordinary subgradient image of every compact set. -/
theorem momentMongeAmpereMeasure_apply_eq_subgradientImage_volume
    {φ V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L φ)
    (hc : ConvexOn ℝ univ φ) (hV : Measurable V)
    {K : Set (Space n)} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward φ = (potentialMeasure V).restrict K)
    {S : Set (Space n)} (hS : IsCompact S) :
    momentMongeAmpereMeasure φ V S = volume (convexSubgradientImage φ S) := by
  have hρ : potentialMeasure φ ≪ volume := withDensity_absolutelyContinuous _ _
  have htarget : (potentialMeasure φ).map (gradient φ) ≪ volume := by
    change MomentMap.gradientPushforward φ ≪ volume
    rw [hpush]
    exact Measure.restrict_le_self.absolutelyContinuous.trans (withDensity_absolutelyContinuous _ _)
  have hA := (isCompact_convexSubgradientImage hLip hS).measurableSet
  have hAsub := subgradientImage_subset_closure_of_weak_momentMap hLip hc hK hKc hpush S
  have hh := setLIntegral_comp_gradient_eq_subgradientImage hLip hc hρ htarget hS
    hV.exp.ennreal_ofReal
  change (∫⁻ x in S, ENNReal.ofReal (Real.exp (V (gradient φ x))) ∂potentialMeasure φ) =
    ∫⁻ p in convexSubgradientImage φ S, ENNReal.ofReal (Real.exp (V p))
      ∂MomentMap.gradientPushforward φ at hh
  rw [hpush] at hh
  rw [← potentialMeasure_withDensity_exp_gradient hLip.continuous.measurable hV,
    withDensity_apply _ hS.measurableSet, hh,
    ← withDensity_apply _ hA, restrict_potentialMeasure_withDensity_exp hV hK]
  have hvol : volume.restrict K = volume.restrict (closure K) :=
    (Measure.restrict_congr_set
      (closure_ae_eq_of_null_frontier (hKc.addHaar_frontier volume))).symm
  rw [hvol, Measure.restrict_apply hA, inter_eq_self_of_subset_left hAsub]

end KLS
end

#print axioms KLS.setLIntegral_comp_gradient_eq_subgradientImage
#print axioms KLS.momentMongeAmpereMeasure_apply_eq_subgradientImage_volume

import KLS.FiniteConjugateC1
import KLS.StrictConvexSubgradientInterior
import KLS.MomentAlexandrovOpen

/-!
# Actual inverse transport through the finite conjugate

The conjugate gradient reverses the primal gradient almost everywhere. On
sets inside the genuine conjugate interior, its relative support image has
the exact transported mass, including weighted versions. The source is only
Lipschitz and strictly convex; source C1 is not assumed.
-/

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology NNReal ENNReal

noncomputable section
namespace KLS

variable {n : ℕ}

theorem convexSubgradient_subset_interior_momentLegendreDomain
    {u : Space n → ℝ} (hu : Continuous u) (hc : StrictConvexOn ℝ univ u)
    (hD : (interior (momentLegendreDomain u)).Nonempty) (x : Space n) :
    convexSubgradient u x ⊆ interior (momentLegendreDomain u) :=
  convexSubgradient_subset_interior_of_strictConvexOn hu hc
    (convex_momentLegendreDomain u) hD
    (fun _ _ hp => mem_momentLegendreDomain_of_support_any_normalization hp) x

theorem gradient_finiteLegendrePotential_gradient_ae
    {u : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : StrictConvexOn ℝ univ u)
    (hD : (interior (momentLegendreDomain u)).Nonempty)
    {ρ : Measure (Space n)} (hρ : ρ ≪ volume) :
    ∀ᵐ x ∂ρ, gradient (finiteLegendrePotential u) (gradient u x) = x := by
  filter_upwards [hρ.ae_le (hLip.ae_differentiableAt (μ := volume))] with x hx
  have hp := gradient_mem_convexSubgradient hc.convexOn hx
  exact gradient_finiteLegendrePotential_eq_of_mem_convexSubgradient hLip.continuous hc
    (convexSubgradient_subset_interior_momentLegendreDomain hLip.continuous hc hD x hp) hp

theorem map_gradient_finiteLegendrePotential_inverse
    {u : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : StrictConvexOn ℝ univ u)
    (hD : (interior (momentLegendreDomain u)).Nonempty)
    {ρ μ : Measure (Space n)} (hρ : ρ ≪ volume)
    (hmap : ρ.map (gradient u) = μ) :
    μ.map (gradient (finiteLegendrePotential u)) = ρ := by
  rw [← hmap, Measure.map_map (measurable_gradient _) (measurable_gradient _)]
  calc
    ρ.map (gradient (finiteLegendrePotential u) ∘ gradient u) = ρ.map id :=
      Measure.map_congr (gradient_finiteLegendrePotential_gradient_ae hLip hc hD hρ)
    _ = ρ := Measure.map_id

theorem convexSubgradientImageOn_finiteLegendrePotential_eq_gradient_image
    {u : Space n → ℝ} (hu : Continuous u) (hc : StrictConvexOn ℝ univ u)
    {S : Set (Space n)} (hS : S ⊆ interior (momentLegendreDomain u)) :
    convexSubgradientImageOn (finiteLegendrePotential u) (momentLegendreDomain u) S =
      gradient (finiteLegendrePotential u) '' S := by
  ext x
  constructor
  · rintro ⟨p, hp, hx⟩
    rw [convexSubgradientOn_finiteLegendrePotential_eq_singleton hu hc (hS hp),
      mem_singleton_iff] at hx
    exact ⟨p, hp, hx.symm⟩
  · rintro ⟨p, hp, rfl⟩
    refine ⟨p, hp, ?_⟩
    rw [convexSubgradientOn_finiteLegendrePotential_eq_singleton hu hc (hS hp)]
    exact mem_singleton _

theorem isSigmaCompact_gradient_finiteLegendrePotential_image
    {u : Space n → ℝ} (hu : Continuous u) (hc : StrictConvexOn ℝ univ u)
    {S : Set (Space n)} (hS : IsSigmaCompact S)
    (hSD : S ⊆ interior (momentLegendreDomain u)) :
    IsSigmaCompact (gradient (finiteLegendrePotential u) '' S) :=
  hS.image_of_continuousOn
    ((continuousOn_gradient_finiteLegendrePotential_of_strictConvexOn hu hc).mono hSD)

/-- The image/preimage equality uses source differentiability only almost
everywhere, supplied by the actual Lipschitz theorem. -/
theorem preimage_gradient_eq_inverse_gradient_image_ae
    {u : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : StrictConvexOn ℝ univ u) {ρ : Measure (Space n)} (hρ : ρ ≪ volume)
    {S : Set (Space n)} (hSD : S ⊆ interior (momentLegendreDomain u)) :
    (gradient u ⁻¹' S) =ᵐ[ρ] gradient (finiteLegendrePotential u) '' S := by
  filter_upwards [hρ.ae_le (hLip.ae_differentiableAt (μ := volume))] with x hx
  apply propext
  constructor
  · intro hxs
    refine ⟨gradient u x, hxs, ?_⟩
    exact gradient_finiteLegendrePotential_eq_of_mem_convexSubgradient hLip.continuous hc
      (hSD hxs) (gradient_mem_convexSubgradient hc.convexOn hx)
  · rintro ⟨p, hp, heq⟩
    have hs := mem_convexSubgradient_gradient_finiteLegendrePotential hLip.continuous hc (hSD hp)
    rw [heq] at hs
    have hpg := eq_gradient_of_mem_convexSubgradient hx hs
    change gradient u x ∈ S
    rw [← hpg]
    exact hp

theorem measure_gradient_finiteLegendrePotential_image_eq
    {u : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : StrictConvexOn ℝ univ u) {ρ : Measure (Space n)} (hρ : ρ ≪ volume)
    {S : Set (Space n)} (hS : MeasurableSet S)
    (hSD : S ⊆ interior (momentLegendreDomain u)) :
    (ρ.map (gradient u)) S = ρ (gradient (finiteLegendrePotential u) '' S) := by
  rw [Measure.map_apply (measurable_gradient _) hS]
  exact measure_congr (preimage_gradient_eq_inverse_gradient_image_ae hLip hc hρ hSD)

/-- Weighted reciprocal mass identity on the actual inverse image. -/
theorem setLIntegral_comp_gradient_finiteLegendrePotential_eq_image
    {u : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : StrictConvexOn ℝ univ u) {ρ : Measure (Space n)} (hρ : ρ ≪ volume)
    {S : Set (Space n)} (hS : MeasurableSet S)
    (hA : MeasurableSet (gradient (finiteLegendrePotential u) '' S))
    (hSD : S ⊆ interior (momentLegendreDomain u))
    {w : Space n → ℝ≥0∞} (hw : Measurable w) :
    ∫⁻ p in S, w (gradient (finiteLegendrePotential u) p) ∂ρ.map (gradient u) =
      ∫⁻ x in gradient (finiteLegendrePotential u) '' S, w x ∂ρ := by
  have hmeas : Measurable (fun p => w (gradient (finiteLegendrePotential u) p)) :=
    hw.comp (measurable_gradient _)
  rw [← lintegral_indicator hS, ← lintegral_indicator hA,
    lintegral_map (hmeas.indicator hS) (measurable_gradient u)]
  apply lintegral_congr_ae
  filter_upwards [hρ.ae_le (hLip.ae_differentiableAt (μ := volume)),
    preimage_gradient_eq_inverse_gradient_image_ae hLip hc hρ hSD] with x hx heq
  have hiff : gradient u x ∈ S ↔ x ∈ gradient (finiteLegendrePotential u) '' S :=
    Iff.of_eq heq
  by_cases hxs : gradient u x ∈ S
  · have hxa := hiff.mp hxs
    simp only [indicator_of_mem hxs, indicator_of_mem hxa]
    rw [gradient_finiteLegendrePotential_eq_of_mem_convexSubgradient hLip.continuous hc
      (hSD hxs) (gradient_mem_convexSubgradient hc.convexOn hx)]
  · have hxa := mt hiff.mpr hxs
    simp only [indicator_of_notMem hxs, indicator_of_notMem hxa]

end KLS
end

#print axioms KLS.map_gradient_finiteLegendrePotential_inverse
#print axioms KLS.convexSubgradientImageOn_finiteLegendrePotential_eq_gradient_image
#print axioms KLS.measure_gradient_finiteLegendrePotential_image_eq
#print axioms KLS.setLIntegral_comp_gradient_finiteLegendrePotential_eq_image

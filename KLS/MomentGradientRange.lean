import KLS.BoundedMomentMapExistence
import KLS.ConvexSubgradient

/-!
# Global subgradient range in the closed convex target

Almost-everywhere gradient containment becomes containment of every ordinary
subgradient. Strong separation and monotonicity rule out a slope outside the
closed convex target, using a nearby point in the dense differentiability set.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

noncomputable section
namespace KLS

theorem volume_absolutelyContinuous_potentialMeasure_of_measurable {n : ℕ} {φ : Space n → ℝ}
    (hφ : Measurable φ) : volume ≪ potentialMeasure φ := by
  apply withDensity_absolutelyContinuous'
    (hφ.neg.exp.ennreal_ofReal.aemeasurable)
  exact Eventually.of_forall fun x => ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)

/-- A closed convex set containing almost every gradient contains every
supporting slope, including at nondifferentiability points. -/
theorem convexSubgradient_subset_of_ae_gradient_mem
    {n : ℕ} {φ : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L φ)
    (hconvex : ConvexOn ℝ Set.univ φ) {K : Set (Space n)}
    (hKclosed : IsClosed K) (hKconvex : Convex ℝ K)
    (hgrad : ∀ᵐ z ∂(volume : Measure (Space n)), gradient φ z ∈ K) (x : Space n) :
    convexSubgradient φ x ⊆ K := by
  intro p hp
  by_contra hpK
  obtain ⟨f, c, hfK, hfp⟩ := geometric_hahn_banach_closed_point hKconvex hKclosed hpK
  let u : Space n := (InnerProductSpace.toDual ℝ (Space n)).symm f
  have hu (q : Space n) : inner ℝ u q = f q := InnerProductSpace.toDual_symm_apply
  have hgood : ∀ᵐ z ∂(volume : Measure (Space n)),
      DifferentiableAt ℝ φ z ∧ gradient φ z ∈ K :=
    (hLip.ae_differentiableAt (μ := volume)).and hgrad
  have hdense := Measure.dense_of_ae hgood
  let δ : ℝ := (f p - c) / (2 * L + 1)
  have hden : 0 < 2 * (L : ℝ) + 1 := by positivity
  have hδ : 0 < δ := div_pos (sub_pos.mpr hfp) hden
  have hδeq : δ * (2 * L + 1) = f p - c := div_mul_cancel₀ _ hden.ne'
  obtain ⟨z, hzgood, hzdist⟩ := hdense.exists_dist_lt (x + u) hδ
  have hq : gradient φ z ∈ convexSubgradient φ z := gradient_mem_convexSubgradient hconvex hzgood.1
  have hpq : ‖p - gradient φ z‖ ≤ 2 * (L : ℝ) :=
    (norm_sub_le _ _).trans (by linarith [norm_le_of_mem_convexSubgradient hLip hp,
      norm_le_of_mem_convexSubgradient hLip hq])
  have herr : ‖(x + u) - z‖ ≤ δ := by simpa only [dist_eq_norm] using hzdist.le
  have hmono := convexSubgradient_monotone hp hq
  have hsplit : x - z = ((x + u) - z) - u := by abel
  rw [hsplit, inner_sub_right] at hmono
  have hi : inner ℝ (p - gradient φ z) u ≤
      ‖p - gradient φ z‖ * ‖(x + u) - z‖ := by
    exact (by linarith : inner ℝ (p - gradient φ z) u ≤
      inner ℝ (p - gradient φ z) ((x + u) - z)).trans (real_inner_le_norm _ _)
  have hibound : inner ℝ (p - gradient φ z) u ≤ 2 * (L : ℝ) * δ :=
    hi.trans (mul_le_mul hpq herr (norm_nonneg _) (by positivity))
  rw [real_inner_comm u (p - gradient φ z), inner_sub_right, hu, hu] at hibound
  have hfc := hfK (gradient φ z) hzgood.2
  nlinarith

/-- The actual gradient transport from a finite continuous potential upgrades
an almost-everywhere target-support condition to a global subgradient bound. -/
theorem convexSubgradient_subset_of_momentMap
    {n : ℕ} {μ : Measure (Space n)} {φ : Space n → ℝ} {L : ℝ≥0}
    (hLip : LipschitzWith L φ) (hconvex : ConvexOn ℝ Set.univ φ)
    (hmap : (potentialMeasure φ).map (gradient φ) = μ) {K : Set (Space n)}
    (hKclosed : IsClosed K) (hKconvex : Convex ℝ K) (hK : ∀ᵐ p ∂μ, p ∈ K)
    (x : Space n) : convexSubgradient φ x ⊆ K := by
  have hsource : ∀ᵐ z ∂potentialMeasure φ, gradient φ z ∈ K := by
    apply ae_of_ae_map (measurable_gradient φ).aemeasurable
    simpa only [hmap] using hK
  have hvolume : ∀ᵐ z ∂(volume : Measure (Space n)), gradient φ z ∈ K :=
    (volume_absolutelyContinuous_potentialMeasure_of_measurable hLip.continuous.measurable).ae_le hsource
  exact convexSubgradient_subset_of_ae_gradient_mem hLip hconvex hKclosed hKconvex hvolume x

/-- The constructed bounded moment map has all its supporting slopes in any
closed convex set carrying the target measure. -/
theorem IsIsotropic.exists_bounded_momentMap_with_subgradient_range
    {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : IsIsotropic μ)
    (L : ℝ≥0) (hbound : ∀ᵐ y ∂μ, ‖y‖ ≤ L) {K : Set (Space n)}
    (hKclosed : IsClosed K) (hKconvex : Convex ℝ K) (hK : ∀ᵐ p ∂μ, p ∈ K) :
    ∃ ψ : C(Space n, ℝ), LipschitzWith L ψ ∧ ConvexOn ℝ Set.univ ψ ∧
      IsProbabilityMeasure (potentialMeasure ψ) ∧
      (potentialMeasure ψ).map (gradient ψ) = μ ∧
      ∀ x, convexSubgradient ψ x ⊆ K := by
  obtain ⟨ψ, hLip, hconvex, hprob, hmap⟩ := hμ.exists_bounded_momentMap L hbound
  exact ⟨ψ, hLip, hconvex, hprob, hmap,
    convexSubgradient_subset_of_momentMap hLip hconvex hmap hKclosed hKconvex hK⟩

end KLS
end

#print axioms KLS.convexSubgradient_subset_of_ae_gradient_mem
#print axioms KLS.convexSubgradient_subset_of_momentMap
#print axioms KLS.IsIsotropic.exists_bounded_momentMap_with_subgradient_range

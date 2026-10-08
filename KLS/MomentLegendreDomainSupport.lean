import KLS.MomentLegendreRegularity
import KLS.MomentGradientRange
import KLS.RademacherOnOpen

/-!
# The true conjugate domain and the target support

For an actual moment transport with convex target support, the closure of the
finite conjugate domain is exactly that support. Absolute continuity of a
probability target identifies their interiors and locates the inverse equation
on the actual target domain.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

noncomputable section
namespace KLS

/-- Finiteness of a contact value does not require an additive normalization of
the potential; only its exact real value needs the zero normalization. -/
theorem mem_momentLegendreDomain_of_support_any_normalization
    {n : ℕ} {φ : Space n → ℝ} {x p : Space n} (hp : p ∈ convexSubgradient φ x) :
    p ∈ momentLegendreDomain φ := by
  have hle : normalizedLegendreTransform φ p ≤ ENNReal.ofReal (inner ℝ p x - φ x) := by
    apply iSup_le
    intro z
    apply ENNReal.ofReal_le_ofReal
    have h := hp z
    rw [inner_sub_right] at h
    linarith
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle

theorem measurableSet_momentLegendreDomain {n : ℕ} (φ : Space n → ℝ) :
    MeasurableSet (momentLegendreDomain φ) := by
  change MeasurableSet ((normalizedLegendreTransform φ) ⁻¹' ({∞} : Set ℝ≥0∞)ᶜ)
  exact (measurable_normalizedLegendreTransform φ) ((measurableSet_singleton (∞ : ℝ≥0∞)).compl)

/-- Global containment of supporting slopes controls the whole finite
conjugate domain, not only gradient values. -/
theorem momentLegendreDomain_subset_of_subgradient_range
    {n : ℕ} {φ : Space n → ℝ} (hcont : Continuous φ)
    (hconvex : ConvexOn ℝ Set.univ φ) {K : Set (Space n)}
    (hKclosed : IsClosed K) (hKconvex : Convex ℝ K)
    (hrange : ∀ x, convexSubgradient φ x ⊆ K) : momentLegendreDomain φ ⊆ K := by
  intro p hp
  by_contra hpK
  obtain ⟨f, c, hfK, hfp⟩ := geometric_hahn_banach_closed_point hKconvex hKclosed hpK
  let u : Space n := (InnerProductSpace.toDual ℝ (Space n)).symm f
  have hu (q : Space n) : inner ℝ u q = f q := InnerProductSpace.toDual_symm_apply
  let D : ℝ := (normalizedLegendreTransform φ p).toReal
  have hD : 0 ≤ D := ENNReal.toReal_nonneg
  let t : ℝ := (|φ 0| + D + 1) / (f p - c)
  have hgap : 0 < f p - c := sub_pos.mpr hfp
  have ht : 0 < t := div_pos (by positivity) hgap
  have hteq : t * (f p - c) = |φ 0| + D + 1 := div_mul_cancel₀ _ hgap.ne'
  obtain ⟨q, hq⟩ := convexSubgradient_nonempty hcont hconvex (t • u)
  have hqK := hrange (t • u) hq
  have hq0 := hq 0
  have hqinner : inner ℝ q (t • u) = t * f q := by
    rw [inner_smul_right, real_inner_comm u q, hu]
  simp only [zero_sub, inner_neg_right] at hq0
  rw [hqinner] at hq0
  have hyoung := normalizedLegendreTransform_young φ hp (t • u)
  rw [inner_smul_right, real_inner_comm u p, hu] at hyoung
  change t * f p ≤ φ (t • u) + D at hyoung
  have hqsep := mul_lt_mul_of_pos_left (hfK q hqK) ht
  have hφ0 := le_abs_self (φ 0)
  nlinarith

/-- The actual target is concentrated on the genuine finite conjugate domain. -/
theorem ae_mem_momentLegendreDomain_of_momentMap
    {n : ℕ} {μ : Measure (Space n)} {φ : Space n → ℝ} {L : ℝ≥0}
    (hLip : LipschitzWith L φ) (hconvex : ConvexOn ℝ Set.univ φ)
    (hmap : (potentialMeasure φ).map (gradient φ) = μ) :
    ∀ᵐ p ∂μ, p ∈ momentLegendreDomain φ := by
  have hac : potentialMeasure φ ≪ volume := withDensity_absolutelyContinuous _ _
  have hsource : ∀ᵐ x ∂potentialMeasure φ, gradient φ x ∈ momentLegendreDomain φ := by
    filter_upwards [hac.ae_le (hLip.ae_differentiableAt (μ := volume))] with x hx
    exact mem_momentLegendreDomain_of_support_any_normalization (gradient_mem_convexSubgradient hconvex hx)
  rw [← hmap]
  exact (ae_map_iff (measurable_gradient φ).aemeasurable
    (measurableSet_momentLegendreDomain φ)).mpr hsource

/-- Exact support identification for a convex target support. -/
theorem closure_momentLegendreDomain_eq_support
    {n : ℕ} {μ : Measure (Space n)} {φ : Space n → ℝ} {L : ℝ≥0}
    (hLip : LipschitzWith L φ) (hconvex : ConvexOn ℝ Set.univ φ)
    (hmap : (potentialMeasure φ).map (gradient φ) = μ)
    (hsupport : Convex ℝ μ.support) : closure (momentLegendreDomain φ) = μ.support := by
  apply subset_antisymm
  · apply closure_minimal _ μ.isClosed_support
    exact momentLegendreDomain_subset_of_subgradient_range hLip.continuous hconvex
      μ.isClosed_support hsupport
      (convexSubgradient_subset_of_momentMap hLip hconvex hmap μ.isClosed_support hsupport μ.support_mem_ae)
  · apply Measure.support_subset_of_isClosed isClosed_closure
    filter_upwards [ae_mem_momentLegendreDomain_of_momentMap hLip hconvex hmap] with p hp
    exact subset_closure hp

/-- Absolute continuity of the actual probability target supplies nonempty
interior and identifies the finite conjugate's interior with the target's. -/
theorem interior_momentLegendreDomain_eq_interior_support
    {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    {φ : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L φ)
    (hconvex : ConvexOn ℝ Set.univ φ)
    (hmap : (potentialMeasure φ).map (gradient φ) = μ)
    (hμac : μ ≪ volume) (hsupport : Convex ℝ μ.support) :
    (interior (momentLegendreDomain φ)).Nonempty ∧
      interior (momentLegendreDomain φ) = interior μ.support := by
  have hmem := ae_mem_momentLegendreDomain_of_momentMap hLip hconvex hmap
  have hgood := convexOn_ae_mem_interior_and_differentiableAt hμac
    (convexOn_normalizedLegendreTransform_toReal φ) hmem
  obtain ⟨p, hp, _⟩ := hgood.exists
  have hne : (interior (momentLegendreDomain φ)).Nonempty := ⟨p, hp⟩
  refine ⟨hne, ?_⟩
  rw [← closure_momentLegendreDomain_eq_support hLip hconvex hmap hsupport]
  exact ((convex_momentLegendreDomain φ).interior_closure_eq_interior_of_nonempty_interior hne).symm

end KLS
end

#print axioms KLS.closure_momentLegendreDomain_eq_support
#print axioms KLS.interior_momentLegendreDomain_eq_interior_support

import KLS.LocalizedMomentTransport
import KLS.ReciprocalAlexandrovBounds
import KLS.TruncatedConjugateAgreement

open MeasureTheory InnerProductSpace Matrix Set Filter Metric
open scoped Topology ENNReal NNReal ContDiff
noncomputable section
namespace KLS
variable {n : ℕ}

lemma ball_subset_truncatedConjugateAgreementRegion_of_quadratic_closeness
    {u : Space n → ℝ} (hu : Continuous u) (hc : StrictConvexOn ℝ univ u)
    {c R δ : ℝ} (hR : 0 < R) (hδ : δ ≤ R ^ 2 / 16)
    (hclose : ∀ x ∈ closedBall (0 : Space n) R,
      |u x - centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 c x| ≤ δ) :
    ball (0 : Space n) (R / 4) ⊆ truncatedConjugateAgreementRegion u (R + 1) := by
  intro p hp
  refine ⟨ball_subset_interior_momentLegendreDomain_of_quadratic_closeness hu hc.convexOn
    hR hδ hclose hp, ?_⟩
  have hx := interior_subset
    (gradient_finiteLegendrePotential_mem_interior_closedBall_of_quadratic_closeness hu hc hR hδ hclose hp)
  change dist (gradient (finiteLegendrePotential u) p) 0 ≤ R at hx
  rw [dist_zero_right] at hx
  change ‖gradient (finiteLegendrePotential u) p‖ < R + 1
  linarith

lemma gradient_inverse_gradient_of_contDiff_one
    {u : Space n → ℝ} (hu : ContDiff ℝ 1 u) (hc : StrictConvexOn ℝ univ u)
    {p : Space n} (hp : p ∈ interior (momentLegendreDomain u)) :
    gradient u (gradient (finiteLegendrePotential u) p) = p := by
  have hh := mem_convexSubgradient_gradient_finiteLegendrePotential hu.continuous hc hp
  rw [convexSubgradient_eq_singleton_of_differentiableAt hc.convexOn
    (hu.differentiable (by norm_num) _), mem_singleton_iff] at hh
  exact hh.symm

/-- The actual reciprocal density is continuous and obeys the reciprocal
pointwise bound on every central slope, using the localized inverse contact. -/
theorem reciprocal_density_log_bound_of_quadratic_closeness
    {u V : Space n → ℝ} (hu : ContDiff ℝ 1 u) (hc : StrictConvexOn ℝ univ u)
    (hV : Continuous V) {c R δ ε : ℝ} (hR : 0 < R) (hδ : δ ≤ R ^ 2 / 16)
    (hclose : ∀ x ∈ closedBall (0 : Space n) R,
      |u x - centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 c x| ≤ δ)
    (hdensity : ∀ x ∈ closedBall (0 : Space n) R,
      |Real.exp (-u x + V (gradient u x)) - 1| ≤ ε ^ 2)
    {p : Space n} (hp : p ∈ ball (0 : Space n) (R / 4)) :
    ContinuousAt (fun q => Real.exp (-V q + u (gradient (finiteLegendrePotential u) q))) p ∧
      -ε ^ 2 ≤ Real.log (Real.exp (-V p + u (gradient (finiteLegendrePotential u) p))) := by
  have hpD := ball_subset_interior_momentLegendreDomain_of_quadratic_closeness
    hu.continuous hc.convexOn hR hδ hclose hp
  have hx := interior_subset
    (gradient_finiteLegendrePotential_mem_interior_closedBall_of_quadratic_closeness
      hu.continuous hc hR hδ hclose hp)
  refine ⟨Real.continuous_exp.continuousAt.comp (hV.continuousAt.neg.add (hu.continuous.continuousAt.comp
    (continuousAt_gradient_finiteLegendrePotential_of_strictConvexOn hu.continuous hc hpD))), ?_⟩
  have hh := (abs_le.mp (hdensity _ hx)).2
  rw [gradient_inverse_gradient_of_contDiff_one hu hc hpD] at hh
  have hlog := Real.log_le_sub_one_of_pos (Real.exp_pos (-u (gradient (finiteLegendrePotential u) p) + V p))
  rw [Real.log_exp] at hlog ⊢
  linarith

/-- The reciprocal weak moment equation becomes a local genuine Alexandrov
equation for a globally finite convex truncation, agreeing with the conjugate
throughout the central ball. -/
theorem localized_truncatedConjugate_alexandrov_equation
    {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : StrictConvexOn ℝ univ u) (hV : Measurable V)
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    {c R δ : ℝ} (hR : 0 < R) (hδ : δ ≤ R ^ 2 / 16)
    (hclose : ∀ x ∈ closedBall (0 : Space n) R,
      |u x - centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 c x| ≤ δ)
    {S : Set (Space n)} (hS : IsOpen S) (hSU : S ⊆ ball (0 : Space n) (R / 4)) :
    volume (convexSubgradientImage (truncatedLegendrePotential u (R + 1)) S) =
      ∫⁻ p in S, ENNReal.ofReal (Real.exp (-V p + u (gradient (finiteLegendrePotential u) p))) ∂volume := by
  have hSD := hSU.trans
    (ball_subset_interior_momentLegendreDomain_of_quadratic_closeness hLip.continuous hc.convexOn hR hδ hclose)
  have hSK := hSU.trans (ball_subset_closedBall.trans
    (closedBall_subset_target_of_quadratic_closeness hLip hc.convexOn hK hKc hpush hR hδ hclose))
  rw [convexSubgradientImage_truncatedLegendrePotential_eq_relative hLip.continuous hc
    (hSU.trans (ball_subset_truncatedConjugateAgreementRegion_of_quadratic_closeness
      hLip.continuous hc hR hδ hclose)),
    ← conjugateMongeAmpereMeasure_apply_eq_relativeSubgradientImage_volume hLip hc hV
      hK.measurableSet hpush (isSigmaCompact_of_isOpen_space hS) hSD hSK,
    conjugateMongeAmpereMeasure, withDensity_apply _ hS.measurableSet]
  rfl

end KLS
end

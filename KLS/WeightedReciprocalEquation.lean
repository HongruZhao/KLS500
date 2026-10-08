import KLS.WeightedLocalizedTransport
import KLS.LocalizedReciprocalEquation

open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff NNReal ENNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

def weightedConjugateDensity (u W V : Space n → ℝ) (p : Space n) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-V p + W (gradient (finiteLegendrePotential u) p)))

def weightedConjugateMeasure (u W V : Space n → ℝ) : Measure (Space n) :=
  volume.withDensity (weightedConjugateDensity u W V)

lemma weighted_potentialMeasure_withDensity_exp_inverseGradient
    {u W V : Space n → ℝ} (hW : Measurable W) (hV : Measurable V) :
    (potentialMeasure V).withDensity
      (fun p => ENNReal.ofReal (Real.exp (W (gradient (finiteLegendrePotential u) p)))) =
      weightedConjugateMeasure u W V := by
  rw [potentialMeasure, ← withDensity_mul volume
    (f := fun p => ENNReal.ofReal (Real.exp (-V p)))
    (g := fun p => ENNReal.ofReal (Real.exp (W (gradient (finiteLegendrePotential u) p))))
    hV.neg.exp.ennreal_ofReal ((hW.comp (measurable_gradient _)).exp.ennreal_ofReal)]
  congr 1
  funext p
  simp only [Pi.mul_apply, weightedConjugateDensity,
    ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]

theorem weightedConjugateMeasure_eq_relativeSubgradientImage_volume
    {u W V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : StrictConvexOn ℝ univ u) (hW : Measurable W) (hV : Measurable V)
    {K : Set (Space n)} (hK : MeasurableSet K)
    (hpush : (potentialMeasure W).map (gradient u) = (potentialMeasure V).restrict K)
    {S : Set (Space n)} (hS : IsSigmaCompact S)
    (hSD : S ⊆ interior (momentLegendreDomain u)) (hSK : S ⊆ K) :
    weightedConjugateMeasure u W V S =
      volume (convexSubgradientImageOn (finiteLegendrePotential u) (momentLegendreDomain u) S) := by
  have hSm := measurableSet_of_isSigmaCompact_space hS
  have hA := measurableSet_of_isSigmaCompact_space
    (isSigmaCompact_gradient_finiteLegendrePotential_image hLip.continuous hc hS hSD)
  have hρ : potentialMeasure W ≪ volume := withDensity_absolutelyContinuous _ _
  have hh := setLIntegral_comp_gradient_finiteLegendrePotential_eq_image hLip hc
    hρ hSm hA hSD hW.exp.ennreal_ofReal
  rw [hpush] at hh
  have hcancel : (potentialMeasure W).withDensity (fun x => ENNReal.ofReal (Real.exp (W x))) =
      volume := by
    simpa only [Measure.restrict_univ] using
      restrict_potentialMeasure_withDensity_exp (V := W) (K := univ) hW MeasurableSet.univ
  rw [← withDensity_apply _ hSm, ← restrict_withDensity hK,
    weighted_potentialMeasure_withDensity_exp_inverseGradient hW hV,
    Measure.restrict_apply hSm, inter_eq_self_of_subset_left hSK,
    ← withDensity_apply _ hA, hcancel] at hh
  rw [convexSubgradientImageOn_finiteLegendrePotential_eq_gradient_image hLip.continuous hc hSD]
  exact hh

theorem weighted_reciprocal_density_log_bound_of_quadratic_closeness
    {u W V : Space n → ℝ} (hu : ContDiff ℝ 1 u) (hc : StrictConvexOn ℝ univ u)
    (hW : Continuous W) (hV : Continuous V) {c R δ ε : ℝ} (hR : 0 < R) (hδ : δ ≤ R ^ 2 / 16)
    (hclose : ∀ x ∈ closedBall (0 : Space n) R,
      |u x - centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 c x| ≤ δ)
    (hdensity : ∀ x ∈ closedBall (0 : Space n) R,
      |Real.exp (-W x + V (gradient u x)) - 1| ≤ ε ^ 2)
    {p : Space n} (hp : p ∈ ball (0 : Space n) (R / 4)) :
    ContinuousAt (fun q => Real.exp (-V q + W (gradient (finiteLegendrePotential u) q))) p ∧
      -ε ^ 2 ≤ Real.log (Real.exp (-V p + W (gradient (finiteLegendrePotential u) p))) := by
  have hpD := ball_subset_interior_momentLegendreDomain_of_quadratic_closeness
    hu.continuous hc.convexOn hR hδ hclose hp
  have hx := interior_subset
    (gradient_finiteLegendrePotential_mem_interior_closedBall_of_quadratic_closeness
      hu.continuous hc hR hδ hclose hp)
  refine ⟨Real.continuous_exp.continuousAt.comp (hV.continuousAt.neg.add (hW.continuousAt.comp
    (continuousAt_gradient_finiteLegendrePotential_of_strictConvexOn hu.continuous hc hpD))), ?_⟩
  have hh := (abs_le.mp (hdensity _ hx)).2
  rw [gradient_inverse_gradient_of_contDiff_one hu hc hpD] at hh
  have hlog := Real.log_le_sub_one_of_pos
    (Real.exp_pos (-W (gradient (finiteLegendrePotential u) p) + V p))
  rw [Real.log_exp] at hlog ⊢
  linarith

/-- The reciprocal weighted equation becomes an ordinary local Alexandrov
equation for the actual finite convex truncation of the conjugate. -/
theorem weighted_localized_truncatedConjugate_alexandrov_equation
    {u W V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : StrictConvexOn ℝ univ u) (hW : Measurable W) (hV : Measurable V)
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : (potentialMeasure W).map (gradient u) = (potentialMeasure V).restrict K)
    {c R δ : ℝ} (hR : 0 < R) (hδ : δ ≤ R ^ 2 / 16)
    (hclose : ∀ x ∈ closedBall (0 : Space n) R,
      |u x - centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 c x| ≤ δ)
    {S : Set (Space n)} (hS : IsOpen S) (hSU : S ⊆ ball (0 : Space n) (R / 4)) :
    volume (convexSubgradientImage (truncatedLegendrePotential u (R + 1)) S) =
      ∫⁻ p in S, ENNReal.ofReal (Real.exp (-V p + W (gradient (finiteLegendrePotential u) p))) := by
  have hSD := hSU.trans
    (ball_subset_interior_momentLegendreDomain_of_quadratic_closeness hLip.continuous hc.convexOn hR hδ hclose)
  have hSK := hSU.trans (ball_subset_closedBall.trans
    (weighted_closedBall_subset_target_of_quadratic_closeness hLip hc.convexOn hW hK hKc hpush hR hδ hclose))
  rw [convexSubgradientImage_truncatedLegendrePotential_eq_relative hLip.continuous hc
    (hSU.trans (ball_subset_truncatedConjugateAgreementRegion_of_quadratic_closeness
      hLip.continuous hc hR hδ hclose)),
    ← weightedConjugateMeasure_eq_relativeSubgradientImage_volume hLip hc hW hV
      hK.measurableSet hpush (isSigmaCompact_of_isOpen_space hS) hSD hSK,
    weightedConjugateMeasure, withDensity_apply _ hS.measurableSet]
  rfl

end KLS
end

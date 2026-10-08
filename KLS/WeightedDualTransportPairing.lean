import KLS.DualTransportPairing
import KLS.WeightedLocalizedTransport

open MeasureTheory InnerProductSpace Matrix Set Filter Metric
open scoped Topology ENNReal NNReal ContDiff
noncomputable section
namespace KLS
variable {n : ℕ}

/-- Fenchel equality and positivity imply a one-sided transport comparison
for the actual dual error. All source and target integrals are integrable. -/
theorem weighted_integral_primal_sub_dual_test_le_transport_difference
    {u W V ψ : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hu : ContDiff ℝ 1 u) (hc : StrictConvexOn ℝ univ u) (hW : Continuous W) (hV : Continuous V)
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : (potentialMeasure W).map (gradient u) = (potentialMeasure V).restrict K)
    {c R δ ε : ℝ} (hR : 0 < R) (hδ : δ ≤ R ^ 2 / 16) (hε : 0 < ε)
    (hclose : ∀ x ∈ closedBall (0 : Space n) R,
      |u x - centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 c x| ≤ δ)
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ ball (0 : Space n) (R / 4)) (hψ0 : ∀ p, 0 ≤ ψ p) :
    0 ≤ (∫ p, (normalizedQuadraticError u 0 0 c ε p - normalizedDualQuadraticError u 0 0 c ε p) * ψ p) ∧
      (∫ p, (normalizedQuadraticError u 0 0 c ε p - normalizedDualQuadraticError u 0 0 c ε p) * ψ p) ≤
      ∫ x, normalizedQuadraticError u 0 0 c ε x *
        (ψ x - Real.exp (-W x + V (gradient u x)) * ψ (gradient u x)) := by
  let w := normalizedQuadraticError u 0 0 c ε
  let v := normalizedDualQuadraticError u 0 0 c ε
  let f : Space n → ℝ := fun x => Real.exp (-W x + V (gradient u x))
  have hw : Continuous w := (contDiff_normalizedQuadraticError hu _ _ _ _).continuous
  have hη : Continuous (fun p => v p * ψ p) :=
    continuous_normalizedDualQuadraticError_mul_test hu.continuous hc hψ hR hδ hclose hs
  have hηc : HasCompactSupport (fun p => v p * ψ p) := hψc.mul_left
  have hηs : tsupport (fun p => v p * ψ p) ⊆ closedBall (0 : Space n) (R / 4) :=
    (tsupport_mul_subset_right (f := v) (g := ψ)).trans (hs.trans ball_subset_closedBall)
  have htarget := weighted_closedBall_subset_target_of_quadratic_closeness hLip hc.convexOn hW.measurable hK hKc hpush hR hδ hclose
  have htransport : (∫ x, f x * (v (gradient u x) * ψ (gradient u x))) = ∫ p, v p * ψ p := by
    rw [integral_comp_gradient_mul_weighted_density hW.measurable hV.measurable
      hK.measurableSet hpush hη.measurable]
    exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun p hp =>
      image_eq_zero_of_notMem_tsupport (f := fun p => v p * ψ p) (fun ht => hp (htarget (hηs ht))))
  have hηint : Integrable (fun x => f x * (v (gradient u x) * ψ (gradient u x))) :=
    integrable_comp_gradient_mul_weighted_density_of_quadratic_closeness hu hc hW hV hη hR hδ hclose hηs
  have hg := continuous_gradient_of_contDiff hu
  have hf : Continuous f := Real.continuous_exp.comp (hW.neg.add (hV.comp hg))
  have hψcomp : HasCompactSupport (ψ ∘ gradient u) :=
    (isCompact_closedBall (0 : Space n) R).of_isClosed_subset (isClosed_tsupport _)
      (tsupport_comp_gradient_subset_closedBall hu hc hR hδ hclose (hs.trans ball_subset_closedBall))
  have hwψ : Integrable (fun x => w x * ψ x) :=
    (hw.mul hψ).integrable_of_hasCompactSupport hψc.mul_left
  have hvψ : Integrable (fun x => v x * ψ x) := hη.integrable_of_hasCompactSupport hηc
  have hfwψ : Integrable (fun x => f x * (w x * ψ (gradient u x))) :=
    (hf.mul (hw.mul (hψ.comp hg))).integrable_of_hasCompactSupport hψcomp.mul_left.mul_left
  have hle : (∫ x, f x * (w x * ψ (gradient u x))) ≤ ∫ p, v p * ψ p := by
    rw [← htransport]
    apply integral_mono hfwψ hηint
    intro x
    have he := normalizedDualQuadraticError_gradient_identity hu hc.convexOn 0 0 c hε.ne' x
    have hvw : w x ≤ v (gradient u x) := by dsimp only [w, v]; nlinarith [sq_nonneg ‖gradient w x‖]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hvw (hψ0 _)) (Real.exp_nonneg _)
  constructor
  · apply integral_nonneg
    intro p
    dsimp only
    by_cases hp : p ∈ tsupport ψ
    · have hD := interior_subset (ball_subset_interior_momentLegendreDomain_of_quadratic_closeness
        hu.continuous hc.convexOn hR hδ hclose (hs hp))
      exact mul_nonneg (sub_nonneg.mpr (normalizedDualQuadraticError_le_primal c hε hD)) (hψ0 p)
    · rw [image_eq_zero_of_notMem_tsupport hp, mul_zero]
      exact le_rfl
  · have hdiff : (∫ p, (w p - v p) * ψ p) = (∫ p, w p * ψ p) - ∫ p, v p * ψ p := by
      simp_rw [sub_mul]
      exact integral_sub hwψ hvψ
    have hright : (∫ x, w x * (ψ x - f x * ψ (gradient u x))) =
        (∫ x, w x * ψ x) - ∫ x, f x * (w x * ψ (gradient u x)) := by
      have he : (fun x => w x * (ψ x - f x * ψ (gradient u x))) =
          (fun x => w x * ψ x - f x * (w x * ψ (gradient u x))) := by funext x; ring
      rw [he, integral_sub hwψ hfwψ]
    change (∫ p, (w p - v p) * ψ p) ≤ ∫ x, w x * (ψ x - f x * ψ (gradient u x))
    rw [hdiff, hright]
    linarith

end KLS
end

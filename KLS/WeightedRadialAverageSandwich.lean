import KLS.MomentRadialAverageSandwich
import KLS.WeightedDualSubharmonicity
import KLS.WeightedMomentEnergy

open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff NNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

/-- Both genuine radial average inequalities follow from the weighted weak
moment equation. The errors are explicitly epsilon times the squared radius. -/
theorem weighted_radial_average_sandwich (hn : 0 < n)
    {u W V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hu : ContDiff ℝ 1 u) (hc : StrictConvexOn ℝ univ u)
    (hW : Continuous W) (hV : Continuous V)
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : (potentialMeasure W).map (gradient u) = (potentialMeasure V).restrict K)
    {c ε T M t : ℝ} (hε : 0 < ε) (hhalf : ε ≤ 1 / 2) (hT : 0 < T)
    (hsmall : ε * M ≤ T ^ 2 / 16)
    (hbound : ∀ x ∈ closedBall (0 : Space n) T, |normalizedQuadraticError u 0 0 c ε x| ≤ M)
    (hdensity : ∀ x ∈ closedBall (0 : Space n) T,
      |Real.exp (-W x + V (gradient u x)) - 1| ≤ ε ^ 2)
    (ht : 0 < t) (htR : t < T / 64)
    {a : Space n} (ha : a ∈ closedBall (0 : Space n) (T / 64)) :
    normalizedQuadraticError u 0 0 c ε a ≤
      (∫ x, normalizedQuadraticError u 0 0 c ε x * radialAverageKernel (normalizedRadialProfile n) a t x) +
        ε * (T / 32) ^ 2 ∧
    (∫ x, continuousDualError u c ε T x * radialAverageKernel (normalizedRadialProfile n) a t x) -
        ε * (T / 32) ^ 2 ≤ continuousDualError u c ε T a ∧
    continuousDualError u c ε T a ≤ normalizedQuadraticError u 0 0 c ε a := by
  have has : ball a (T / 64) ⊆ ball (0 : Space n) (T / 16) :=
    ball_subset_centered_ball ha (by linarith)
  have hκs := normalizedRadialKernel_tsupport_subset_centered_closedBall ha ht
    (by linarith : T / 64 + t ≤ T / 32)
  have hcont : Continuous (normalizedQuadraticError u 0 0 c ε) :=
    (hLip.continuous.sub (continuous_centeredQuadratic _ _ _ _)).div_const ε
  refine ⟨?_, ?_, continuousDualError_le_primal hLip.continuous hc hε hT hsmall hbound
    ((closedBall_subset_ball (by linarith : T / 64 < T / 4)) ha)⟩
  · apply upper_average_of_subharmonic_quadratic_correction hcont hε.le ht htR
      (by positivity) hκs
    intro ψ hψ hψc hψs hψ0
    have hh := integral_subharmonicNormalizedError_mul_laplacian_nonneg hn hu.continuous hc.convexOn
      (Real.continuous_exp.comp (hW.neg.add (hV.comp (continuous_gradient_of_contDiff hu))))
      (fun _S hS => weighted_moment_alexandrov_equation hLip hc.convexOn hW.measurable hV.measurable
        hK hKc hpush hS) 0 0 c hε hhalf (r := T / 16) (R := T / 8) (by positivity) (by linarith)
      (fun x hx => hdensity x (closedBall_subset_closedBall (by linarith) hx)) hψ hψc (hψs.trans has) hψ0
    simpa only [subharmonicNormalizedError_apply, sub_zero] using hh
  · apply lower_average_of_subharmonic_negative_quadratic_correction
      (continuous_continuousDualError hLip.continuous c ε hT) hε.le ht htR (by positivity) hκs
    intro ψ hψ hψc hψs hψ0
    have hh := weighted_integral_subharmonicNegativeDualError_mul_laplacian_nonneg hn hLip hu hc hW hV
      hK hKc hpush hε (r := T / 16) (s := T / 8) (by positivity) (by linarith)
      (by linarith) hsmall (fun x hx => abs_sub_quadratic_le_of_normalized_bound hε (hbound x hx)) hdensity hψ hψc (hψs.trans has) hψ0
    convert hh using 1
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only
      by_cases hx : x ∈ tsupport (coordinateLaplacian ψ)
      · have hxU : x ∈ ball (0 : Space n) (T / 4) :=
          ball_subset_ball (by linarith : T / 16 ≤ T / 4) (has (hψs (tsupport_coordinateLaplacian_subset ψ hx)))
        rw [continuousDualError_eq_dual hLip.continuous hc hε hT hsmall hbound hxU]
        simp only [subharmonicNegativeDualError, centeredQuadratic, sub_zero, inner_zero_left,
          zero_add, add_zero, matrixAction_one_apply, real_inner_self_eq_norm_sq]
        ring
      · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero, mul_zero]

end KLS
end

import KLS.WeakMomentCenteredTransfer
import KLS.MongeAmpereDifferenceCoercivity
import KLS.MatrixLoewnerUpper

open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped Topology ContDiff NNReal ENNReal Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- The actual Frechet derivative equals its actual coordinate expansion. -/
theorem fderiv_eq_sum_coordinateDerivative (f : Space n → ℝ) (x v : Space n) :
    fderiv ℝ f x v = ∑ i, coordinateDerivative f i x*v i := by
  rw [← inner_gradient_left]
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,coordinateDerivative_eq_gradient,mul_comm]

/-- At an actual symmetric Hessian point, the literal diffusion equals the
 trace and target derivative expression used in three-point MA coercivity. -/
theorem hessianMetricDiffusion_eq_trace_sub_fderiv_at
    (u V f : Space n → ℝ) (x : Space n) (hf : (coordinateHessian f x).IsSymm) :
    hessianMetricDiffusion u V f x =
      ((coordinateHessian u x)⁻¹ * coordinateHessian f x).trace -
        fderiv ℝ V (gradient u x) (gradient f x) := by
  rw [hessianMetricDiffusion,matrix_entrywise_contraction_eq_trace _ _ hf,fderiv_eq_sum_coordinateDerivative]
  simp only [coordinateDerivative_eq_gradient f]

set_option synthInstance.maxHeartbeats 100000 in
-- The translated Euclidean derivative data require additional instance search.
/-- Quantitative centered MA coercivity holds a.e. for the literal weak
 transport potential. The upper Loewner constant is derived from its actual
 gradient Lipschitz bound, with no dimensional loss. -/
theorem weak_moment_centered_difference_coercivity_ae
    {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : ContDiff ℝ 1 V) (hVc : ConvexOn ℝ univ V)
    {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun p => V p - (κ / 2) * ‖p‖ ^ 2))
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K) (h : Space n) :
    ∀ᵐ x ∂(volume : Measure (Space n)),
      (((16/κ)⁻¹)^2/2) *
        (matrixFrobeniusSq (coordinateHessian u (x+h)-coordinateHessian u x) +
          matrixFrobeniusSq (coordinateHessian u (x-h)-coordinateHessian u x)) ≤
      hessianMetricDiffusion u V (symmetricSecondDifference u h) x+symmetricSecondDifference u h x := by
  have hu := moment_contDiff_one_closedTarget hLip hc hV.continuous hK hKc hpush
  have hud := hu.differentiable (by norm_num)
  have hG := weak_moment_gradient_lipschitz_of_uniformlyConvex_target hLip hc hV hVc hκ hstrong hK hKc hpush
  have hAe := weak_moment_ae_hessian_equation_of_gradient_lipschitz hLip hc hV.continuous hK hKc hpush hG
  have hdata : ∀ᵐ x ∂(volume : Measure (Space n)), (coordinateHessian u x).PosDef ∧
      Real.log (coordinateHessian u x).det = -u x+V (gradient u x) ∧
      (((16/κ) • (1 : Matrix (Fin n) (Fin n) ℝ)) - coordinateHessian u x).PosSemidef := by
    filter_upwards [hAe] with x hx
    refine ⟨hx.1,?_,?_⟩
    · rw [hx.2.1,Real.log_exp]
    · apply loewner_upper_of_matrixAction_norm_le hx.1.isHermitian.isSymm
      rw [← hx.2.2.1.fderiv]
      exact norm_fderiv_le_of_lipschitz ℝ hG
  have hplus := (measurePreserving_add_right (volume : Measure (Space n)) h).quasiMeasurePreserving.ae hdata
  have hminus := (measurePreserving_add_right (volume : Measure (Space n)) (-h)).quasiMeasurePreserving.ae hdata
  have hδ := coordinateHessian_symmetricSecondDifference_ae_C11 hud hG h
  have hδG := lipschitz_gradient_symmetricSecondDifference hud hG h
  filter_upwards [hdata,hplus,hminus,hδ,hδG.ae_differentiableAt (μ := volume)] with x hx hp hm hh hd
  have hm' : (coordinateHessian u (x-h)).PosDef ∧
      Real.log (coordinateHessian u (x-h)).det = -u (x-h)+V (gradient u (x-h)) ∧
      (((16/κ) • (1 : Matrix (Fin n) (Fin n) ℝ)) - coordinateHessian u (x-h)).PosSemidef := by
    simpa only [sub_eq_add_neg] using hm
  have hsym := coordinateHessian_isSymm_of_gradient_differentiableAt
    ((symmetricSecondDifference_contDiff hu h).differentiable (by norm_num)) hd
  rw [hessianMetricDiffusion_eq_trace_sub_fderiv_at u V _ x hsym,hh,gradient_symmetricSecondDifference hud]
  exact mongeAmpere_centeredDifference_coercivity_at (hV.differentiable (by norm_num)) hVc x h
    (by positivity) hx.1 hp.1 hm'.1 hx.2.2 hp.2.2 hm'.2.2 hx.2.1 hp.2.1 hm'.2.1

end KLS
end

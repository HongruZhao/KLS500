import KLS.WeakMomentSublevelTail
import KLS.WeakMomentPotentialDrift

open MeasureTheory Set Filter InnerProductSpace
open scoped ContDiff Topology NNReal ENNReal Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- Positivity of the actual inverse-Hessian energy is pointwise matrix
 algebra at any actual positive Hessian point. -/
theorem inverseHessianGradientForm_nonneg_at
    {u : Space n → ℝ} (f : Space n → ℝ) {x : Space n}
    (hx : (coordinateHessian u x).PosDef) : 0 ≤ inverseHessianGradientForm u f x := by
  rw [inverseHessianGradientForm,matrix_quadratic_sum_eq_dotProduct]
  simpa only [star_trivial] using hx.inv.posSemidef.dotProduct_mulVec_nonneg
    (fun i => coordinateDerivative f i x)

/-- The genuine auxiliary test bounds its nonnegative inverse-Hessian
 energy by the cutoff scale times the actual integrable potential drift. -/
theorem weak_moment_potentialSublevelTail_energy_le
    {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hconv : ConvexOn ℝ univ u) (hV : ContDiff ℝ 1 V) (hVc : ConvexOn ℝ univ V)
    {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun p => V p - (κ / 2) * ‖p‖ ^ 2))
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    (x₀ : Space n) {c : ℝ} (hc : 0 < c) :
    (∫ x, c^2*‖deriv (deriv sublevelCutoffProfile) (c*potentialHeight u x₀ x)‖ *
      inverseHessianGradientForm u (potentialHeight u x₀) x ∂potentialMeasure u) ≤
      c*(∫ s, ‖deriv (deriv sublevelCutoffProfile) s‖) *
        ∫ x, ‖hessianMetricDiffusion u V (potentialHeight u x₀) x‖ ∂potentialMeasure u := by
  have hu := moment_contDiff_one_closedTarget hLip hconv hV.continuous hK hKc hpush
  have hLW := weak_moment_integrable_potentialHeight_diffusion
    hLip hconv hV hVc hκ hstrong hK hKc hpush x₀
  rw [(weak_moment_potentialSublevelTail_energy_identity
    hLip hconv hV hVc hκ hstrong hK hKc hpush x₀ hc).2]
  have hp : Integrable (fun x => potentialSublevelTail u x₀ c x *
      hessianMetricDiffusion u V (potentialHeight u x₀) x) (potentialMeasure u) :=
    hLW.bdd_mul (potentialSublevelTail_contDiff_one hu x₀ c).continuous.aestronglyMeasurable
      (Eventually.of_forall fun x => scaledSublevelTail_norm_le hc.le _)
  calc
    _ ≤ ‖∫ x, potentialSublevelTail u x₀ c x *
      hessianMetricDiffusion u V (potentialHeight u x₀) x ∂potentialMeasure u‖ := le_abs_self _
    _ ≤ ∫ x, ‖potentialSublevelTail u x₀ c x *
      hessianMetricDiffusion u V (potentialHeight u x₀) x‖ ∂potentialMeasure u :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x, (c*∫ s, ‖deriv (deriv sublevelCutoffProfile) s‖) *
      ‖hessianMetricDiffusion u V (potentialHeight u x₀) x‖ ∂potentialMeasure u := by
      apply integral_mono hp.norm (hLW.norm.const_mul _)
      intro x
      dsimp only
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (scaledSublevelTail_norm_le hc.le _) (norm_nonneg _)
    _ = _ := integral_const_mul _ _

end KLS
end

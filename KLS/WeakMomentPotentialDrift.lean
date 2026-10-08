import KLS.WeakMomentCenteredCoercivity
import KLS.HessianPotentialDrift

open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped ContDiff Topology NNReal ENNReal Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- At an actual positive Hessian point, the original-potential diffusion
 has no inverse-Hessian growth term. This is only matrix algebra. -/
theorem hessianMetricDiffusion_potential_eq_at_posDef
    (u V : Space n → ℝ) {x : Space n} (hx : (coordinateHessian u x).PosDef) :
    hessianMetricDiffusion u V u x =
      (n : ℝ)-∑ i, coordinateDerivative V i (gradient u x)*(gradient u x) i := by
  rw [hessianMetricDiffusion_eq_trace_sub_fderiv_at u V u x hx.isHermitian.isSymm,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hx.det_pos.ne'),Matrix.trace_one,
    fderiv_eq_sum_coordinateDerivative]
  simp only [Fintype.card_fin]

/-- Finite source mass and an actual Lipschitz source gradient range make
 the original-potential drift integrable as soon as actual Hessians are
 positive almost everywhere. Target C1 suffices. -/
theorem integrable_hessianMetricDiffusion_potential_of_ae_posDef
    {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u) (hV : ContDiff ℝ 1 V)
    [IsFiniteMeasure (potentialMeasure u)]
    (hpos : ∀ᵐ x ∂(volume : Measure (Space n)), (coordinateHessian u x).PosDef) :
    Integrable (hessianMetricDiffusion u V u) (potentialMeasure u) := by
  let F : Space n → ℝ := fun z => (n : ℝ)-∑ i, coordinateDerivative V i z*z i
  have hF : Continuous F := by
    apply continuous_const.sub
    apply continuous_finsetSum
    intro i _
    exact (contDiff_coordinateDerivative hV (m := 0) (by norm_num) i).continuous.mul
      (EuclideanSpace.proj i).continuous
  obtain ⟨D,hD⟩ := (isCompact_closedBall (0 : Space n) (L : ℝ)).bddAbove_image hF.norm.continuousOn
  have hbound (x : Space n) : ‖F (gradient u x)‖ ≤ D := by
    apply hD
    apply mem_image_of_mem
    simpa only [Metric.mem_closedBall,dist_zero_right] using norm_gradient_le_of_lipschitz hLip x
  have hI : Integrable (fun x => F (gradient u x)) (potentialMeasure u) :=
    (integrable_const D).mono'
      (hF.measurable.comp (measurable_gradient u)).aestronglyMeasurable (Eventually.of_forall hbound)
  have hρ : potentialMeasure u ≪ volume := withDensity_absolutelyContinuous _ _
  apply hI.congr
  filter_upwards [hρ.ae_le hpos] with x hx
  exact (hessianMetricDiffusion_potential_eq_at_posDef u V hx).symm

/-- Literal weak transport supplies the actual a.e positive Hessians and
 hence the finite drift integral used by sublevel cutoffs. -/
theorem weak_moment_integrable_potentialHeight_diffusion
    {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hconv : ConvexOn ℝ univ u) (hV : ContDiff ℝ 1 V) (hVc : ConvexOn ℝ univ V)
    {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun p => V p - (κ / 2) * ‖p‖ ^ 2))
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    (x₀ : Space n) :
    Integrable (hessianMetricDiffusion u V (potentialHeight u x₀)) (potentialMeasure u) := by
  have hG := weak_moment_gradient_lipschitz_of_uniformlyConvex_target
    hLip hconv hV hVc hκ hstrong hK hKc hpush
  have hAe := weak_moment_ae_hessian_equation_of_gradient_lipschitz
    hLip hconv hV.continuous hK hKc hpush hG
  have hI := integrable_hessianMetricDiffusion_potential_of_ae_posDef hLip hV (hAe.mono fun _ hx => hx.1)
  simpa only [funext (hessianMetricDiffusion_potentialHeight_eq u V x₀)] using hI

end KLS
end

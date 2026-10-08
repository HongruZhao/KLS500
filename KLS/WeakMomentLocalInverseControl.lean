import KLS.StrongConvexGradientInverse
import KLS.MomentGradientHomeomorph

open MeasureTheory Set Filter Metric InnerProductSpace
open scoped Topology ContDiff NNReal
noncomputable section
namespace KLS
variable {n : ℕ}

/-- The original moment potential has local strong convexity, and its actual
inverse gradient is Lipschitz on the gradient image of each compact convex set. -/
theorem weak_moment_inverse_gradient_lipschitz_on_compact_image
    {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : ContDiff ℝ 1 V) (hVc : ConvexOn ℝ univ V)
    {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun p => V p - (κ / 2) * ‖p‖ ^ 2))
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    {S : Set (Space n)} (hS : IsCompact S) (hSc : Convex ℝ S) :
    ∃ μ : ℝ, ∃ hμ : 0 < μ, StrongConvexOn S μ u ∧
      (∀ x ∈ S, ∀ y ∈ S, μ * ‖y-x‖ ≤ ‖gradient u y-gradient u x‖) ∧
      LipschitzOnWith (⟨μ⁻¹, (inv_pos.mpr hμ).le⟩ : ℝ≥0)
        (gradient (finiteLegendrePotential u)) (gradient u '' S) := by
  obtain ⟨μ,hμ,hsc⟩ := weak_moment_strongConvexOn_compact hLip hc hV hVc hκ hstrong hK hKc hpush hS hSc
  have hd := (moment_contDiff_one_closedTarget hLip hc hV.continuous hK hKc hpush).differentiable
    (by norm_num)
  have hbound := fun x (hx : x ∈ S) y (hy : y ∈ S) =>
    gradient_inverse_norm_bound_of_strongConvexOn hsc hd hx hy
  refine ⟨μ,hμ,hsc,hbound,?_⟩
  apply LipschitzOnWith.of_dist_le_mul
  rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
  rw [moment_gradient_finiteLegendrePotential_gradient hLip hc hV.continuous hK hKc hpush,
    moment_gradient_finiteLegendrePotential_gradient hLip hc hV.continuous hK hKc hpush]
  simp only [dist_eq_norm]
  change ‖x-y‖ ≤ μ⁻¹ * ‖gradient u x-gradient u y‖
  rw [mul_comm,← div_eq_mul_inv]
  apply (le_div_iff₀ hμ).mpr
  have hh := hbound y hy x hx
  nlinarith

/-- The actual gradient of the finite Legendre potential is locally Lipschitz
on the true conjugate interior. Local inverse regularity is derived from the
weak transport equation and the newly proved local strong convexity. -/
theorem weak_moment_finiteLegendre_gradient_locallyLipschitz
    {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : ContDiff ℝ 1 V) (hVc : ConvexOn ℝ univ V)
    {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun p => V p - (κ / 2) * ‖p‖ ^ 2))
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K) :
    LocallyLipschitzOn (interior (momentLegendreDomain u)) (gradient (finiteLegendrePotential u)) := by
  intro p hp
  let g := gradient (finiteLegendrePotential u)
  let S := closedBall (g p) 1
  obtain ⟨μ,hμ,_,_,hbound⟩ := weak_moment_inverse_gradient_lipschitz_on_compact_image
    hLip hc hV hVc hκ hstrong hK hKc hpush (isCompact_closedBall (g p) 1) (convex_closedBall (g p) 1)
  have hg : ContinuousOn g (interior (momentLegendreDomain u)) :=
    continuousOn_gradient_finiteLegendrePotential_of_strictConvexOn hLip.continuous
      (moment_strictConvexOn hLip hc hV.continuous hK.measurableSet hKc hpush)
  have hN : g ⁻¹' S ∈ 𝓝[interior (momentLegendreDomain u)] p :=
    hg p hp (closedBall_mem_nhds (g p) (by norm_num))
  refine ⟨⟨μ⁻¹,(inv_pos.mpr hμ).le⟩,interior (momentLegendreDomain u) ∩ g ⁻¹' S,
    inter_mem self_mem_nhdsWithin hN,hbound.mono ?_⟩
  intro q hq
  refine ⟨g q,hq.2,?_⟩
  exact moment_gradient_gradient_finiteLegendrePotential hLip hc hV.continuous hK hKc hpush hq.1

end KLS
end

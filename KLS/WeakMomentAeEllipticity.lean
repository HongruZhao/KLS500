import KLS.WeakMomentAeHessian

open MeasureTheory Matrix Set Filter InnerProductSpace
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise
noncomputable section
namespace KLS
variable {n : ℕ}

/-- The original weak moment potential has its actual positive Hessian,
 actual gradient derivative, and actual nonlinear equation almost everywhere.
 Gradient Lipschitz regularity is derived, not assumed. -/
theorem weak_moment_ae_hessian_equation_of_uniformlyConvex_target
    {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : ContDiff ℝ 1 V) (hVc : ConvexOn ℝ univ V)
    {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun p => V p - (κ / 2) * ‖p‖ ^ 2))
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K) :
    ∀ᵐ x ∂(volume : Measure (Space n)),
      (coordinateHessian u x).PosDef ∧
      (coordinateHessian u x).det = Real.exp (-u x+V (gradient u x)) ∧
      HasFDerivAt (gradient u) (matrixAction (coordinateHessian u x)) x ∧
      ‖coordinateHessian u x‖ ≤ 16/κ := by
  exact weak_moment_ae_hessian_equation_of_gradient_lipschitz hLip hc hV.continuous hK hKc hpush
    (weak_moment_gradient_lipschitz_of_uniformlyConvex_target hLip hc hV hVc hκ hstrong hK hKc hpush)

/-- Actual almost-everywhere Hessians are uniformly elliptic on every compact
 set. The local constants depend on dimension, 16/kappa, and a positive lower
 bound for the actual density on that set. No Hessian continuity is claimed. -/
theorem weak_moment_ae_hessian_uniformly_elliptic_on_compact
    {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : ContDiff ℝ 1 V) (hVc : ConvexOn ℝ univ V)
    {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun p => V p - (κ / 2) * ‖p‖ ^ 2))
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    {S : Set (Space n)} (hS : IsCompact S) :
    ∃ B μ Λ : ℝ, (∀ x ∈ S, B ≤ -u x+V (gradient u x)) ∧ 0 < μ ∧ 0 < Λ ∧
      ∀ᵐ x ∂(volume : Measure (Space n)), x ∈ S →
        (coordinateHessian u x).PosDef ∧
        (coordinateHessian u x).det = Real.exp (-u x+V (gradient u x)) ∧
        HasFDerivAt (gradient u) (matrixAction (coordinateHessian u x)) x ∧
        ‖coordinateHessian u x‖ ≤ 16/κ ∧
        ∀ v : Space n, μ*‖v‖^2 ≤ inner ℝ v (matrixAction (coordinateHessian u x) v) ∧
          inner ℝ v (matrixAction (coordinateHessian u x) v) ≤ Λ*‖v‖^2 := by
  have hgrad := weak_moment_gradient_lipschitz_of_uniformlyConvex_target
    hLip hc hV hVc hκ hstrong hK hKc hpush
  have hcont : Continuous (fun x => -u x+V (gradient u x)) :=
    hLip.continuous.neg.add (hV.continuous.comp hgrad.continuous)
  obtain ⟨B,hB⟩ := hS.bddBelow_image hcont.continuousOn
  have hBlo (x : Space n) (hx : x ∈ S) : B ≤ -u x+V (gradient u x) := hB (mem_image_of_mem _ hx)
  obtain ⟨μ,Λ,hμ,hΛ,hell⟩ := exists_uniform_ellipticity_of_det_and_norm n (16/κ) (Real.exp B) (Real.exp_pos B)
  refine ⟨B,μ,Λ,hBlo,hμ,hΛ,?_⟩
  filter_upwards [weak_moment_ae_hessian_equation_of_uniformlyConvex_target
    hLip hc hV hVc hκ hstrong hK hKc hpush] with x hx
  intro hxS
  refine ⟨hx.1,hx.2.1,hx.2.2.1,hx.2.2.2,hell _ hx.1.posSemidef hx.2.2.2 ?_⟩
  rw [hx.2.1]
  exact Real.exp_le_exp.mpr (hBlo x hxS)

end KLS
end

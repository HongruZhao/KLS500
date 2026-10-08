import KLS.SmoothHessianAdjugateDivergence
import KLS.HessianAdjugateMollifierLimit

open MeasureTheory Set Filter Matrix
open scoped Topology ContDiff NNReal ENNReal Matrix.Norms.Elementwise
noncomputable section
namespace KLS
variable {n : ℕ}

/-- The actual Hessian mollifications of the original weak moment potential
 converge strongly in every finite absolutely continuous weighted L2 space. -/
theorem weak_moment_hessian_mollify_weighted_L2
    {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : ContDiff ℝ 1 V) (hVc : ConvexOn ℝ univ V)
    {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun p => V p - (κ / 2) * ‖p‖ ^ 2))
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    {μ : Measure (Space n)} [IsFiniteMeasure μ] (hμ : μ ≪ volume) (i j : Fin n) :
    (∀ k, MemLp (fun x => coordinateHessian (mollify k u) x i j) 2 μ) ∧
      MemLp (fun x => coordinateHessian u x i j) 2 μ ∧
      Tendsto (fun k => eLpNorm
        ((fun x => coordinateHessian (mollify k u) x i j) - (fun x => coordinateHessian u x i j)) 2 μ)
        atTop (𝓝 0) :=
  coordinateHessian_mollify_weighted_L2_of_gradient_lipschitz hLip
    (weak_moment_gradient_lipschitz_of_uniformlyConvex_target hLip hc hV hVc hκ hstrong hK hKc hpush) hμ i j

/-- Every column of the adjugate of the actual weak moment Hessian has zero
 distributional divergence. It follows from actual Hessian mollification and
 convergence, with no source C2 or assumed divergence identity. -/
theorem weak_moment_adjugateHessian_integral_column
    {u V ψ : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : ContDiff ℝ 1 V) (hVc : ConvexOn ℝ univ V)
    {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun p => V p - (κ / 2) * ‖p‖ ^ 2))
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) (j : Fin n) :
    (∑ i, ∫ x, (coordinateHessian u x).adjugate i j * coordinateDerivative ψ i x) = 0 := by
  have hG := weak_moment_gradient_lipschitz_of_uniformlyConvex_target
    hLip hc hV hVc hκ hstrong hK hKc hpush
  have hi (i : Fin n) := tendsto_integral_adjugateHessian_mollify_mul hLip hG
    (contDiff_coordinateDerivative hψ (m := 0) (by norm_num) i).continuous
    (hasCompactSupport_coordinateDerivative hψc i) i j
  have hlim := tendsto_finsetSum Finset.univ (fun i _ => hi i)
  have hzero : (fun k => ∑ i, ∫ x, (coordinateHessian (mollify k u) x).adjugate i j *
      coordinateDerivative ψ i x) = fun _ : ℕ => (0 : ℝ) := by
    funext k
    apply smooth_hessian_adjugate_integral_column
      ((mollify_contDiff hLip.continuous.locallyIntegrable k).of_le (by simp))
      (fun x => (weak_moment_mollify_posDef_and_det_lower hLip hc hV.continuous hK hKc hpush k x).1)
      hψ hψc
  rw [hzero] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

end KLS
end

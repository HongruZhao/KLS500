import KLS.WeakMomentExistsTraceEnergy
import KLS.WeakHessianVariance

open MeasureTheory Set Filter Matrix
open scoped ContDiff Topology NNReal ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- Original weak moment transport and isotropy give the certified raw
 trace-square bound for every constant positive semidefinite B. The actual
 weak tensor and all trace-energy and variance inputs are constructed. -/
theorem weak_moment_trace_square_le_twice_trace
    {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : ContDiff ℝ 2 V) (hVc : ConvexOn ℝ univ V)
    {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun p => V p - (κ / 2) * ‖p‖ ^ 2))
    [IsProbabilityMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    (hiso : IsIsotropic (MomentMap.gradientPushforward u))
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.PosSemidef) :
    Integrable (fun x => rawHessianTraceSquare (coordinateHessian u x) B) (potentialMeasure u) ∧
    (∫ x, rawHessianTraceSquare (coordinateHessian u x) B ∂potentialMeasure u) ≤
      2 * (B * B).trace := by
  obtain ⟨T, hTl, hTw, henergy⟩ :=
    weak_moment_exists_third_tensor_with_global_trace_energy
      hLip hc hV hVc hκ hstrong hK hKc hpush
  obtain ⟨hSi, hAi, _, _, _, hhalf⟩ := henergy B hB
  have hG := weak_moment_gradient_lipschitz_of_uniformlyConvex_target
    hLip hc (hV.of_le (by norm_num)) hVc hκ hstrong hK hKc hpush
  have hMA := weak_moment_ae_hessian_equation_of_gradient_lipschitz
    hLip hc hV.continuous hK hKc hpush hG
  have hpos : ∀ᵐ x, (coordinateHessian u x).PosDef := hMA.mono fun _ hx => hx.1
  have hu := moment_contDiff_one_closedTarget hLip hc hV.continuous hK hKc hpush
  have hvar := rawHessianTrace_variance_control_C11 hu hG hpos hTl hTw hiso hB hAi
  exact ⟨hSi, by linarith⟩

end KLS
end

import KLS.WeakMomentLiteralTraceEnergy
import KLS.WeakMomentThirdTensor

open MeasureTheory Set Filter Matrix
open scoped ContDiff Topology NNReal ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- The original weak transport data construct one genuine weak third
 tensor with global trace integrability, the exact energy identity and the
 certified half-trace estimate for every constant positive semidefinite B.
 No tensor, localized balance or global energy premise is supplied. -/
theorem weak_moment_exists_third_tensor_with_global_trace_energy
    {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : ContDiff ℝ 2 V) (hVc : ConvexOn ℝ univ V)
    {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun p => V p - (κ / 2) * ‖p‖ ^ 2))
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K) :
    ∃ T : Space n → Fin n → Matrix (Fin n) (Fin n) ℝ,
      (∀ k i j E, IsCompact E → MemLp (fun x => T x k i j) 2 (volume.restrict E)) ∧
      (∀ k i j, HasLocalWeakCoordinateDerivative
        (fun x => coordinateHessian u x i j) (fun x => T x k i j) k) ∧
      ∀ B : Matrix (Fin n) (Fin n) ℝ, B.PosSemidef →
        Integrable (fun x => rawHessianTraceSquare (coordinateHessian u x) B) (potentialMeasure u) ∧
        Integrable (fun x => rawHessianTraceGradientTerm (coordinateHessian u x) B (T x)) (potentialMeasure u) ∧
        Integrable (fun x => rawHessianTraceTargetTerm
          (coordinateHessian u x) (coordinateHessian V (gradient u x)) B) (potentialMeasure u) ∧
        Integrable (fun x => rawHessianTraceThirdTerm (coordinateHessian u x) B (T x)) (potentialMeasure u) ∧
        (∫ x, rawHessianTraceSquare (coordinateHessian u x) B ∂potentialMeasure u) =
          (∫ x, rawHessianTraceGradientTerm (coordinateHessian u x) B (T x) ∂potentialMeasure u) +
          (∫ x, rawHessianTraceTargetTerm (coordinateHessian u x) (coordinateHessian V (gradient u x)) B
            ∂potentialMeasure u) +
          (∫ x, rawHessianTraceThirdTerm (coordinateHessian u x) B (T x) ∂potentialMeasure u) ∧
        (∫ x, rawHessianTraceGradientTerm (coordinateHessian u x) B (T x) ∂potentialMeasure u) ≤
          (1 / 2 : ℝ) * ∫ x, rawHessianTraceSquare (coordinateHessian u x) B ∂potentialMeasure u := by
  obtain ⟨T, hTl, hTw⟩ := weak_moment_exists_third_tensor
    hLip hc (hV.of_le (by norm_num)) hVc hκ hstrong hK hKc hpush
  refine ⟨T, hTl, hTw, ?_⟩
  intro B hB
  exact weak_moment_global_trace_energy hLip hc hV hVc hκ hstrong hK hKc hpush hTl hTw hB

end KLS
end

import KLS.WeakMomentGlobalTraceEnergy
import KLS.WeakMomentLocalizedTraceBalance

open MeasureTheory Set Filter Matrix
open scoped ContDiff Topology NNReal ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- Literal weak moment transport gives global raw trace integrability,
 the exact trace-energy identity and the certified half-trace estimate.
 The localized balance is proved from genuine weak Hessian evolution.
 Tensor entries are supplied as actual locally L2 weak derivatives of the
 coordinate Hessian; no balance, cutoff-error or energy premise is used. -/
theorem weak_moment_global_trace_energy
    {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : ContDiff ℝ 2 V) (hVc : ConvexOn ℝ univ V)
    {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun p => V p - (κ / 2) * ‖p‖ ^ 2))
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    {T : Space n → Fin n → Matrix (Fin n) (Fin n) ℝ}
    (hTl : ∀ k i j E, IsCompact E → MemLp (fun x => T x k i j) 2 (volume.restrict E))
    (hTw : ∀ k i j, HasLocalWeakCoordinateDerivative
      (fun x => coordinateHessian u x i j) (fun x => T x k i j) k)
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.PosSemidef) :
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
  apply weak_moment_trace_energy_of_localized_balance
    hLip hc hV hVc hκ hstrong hK hKc hpush hTl hTw hB
  intro χ hχ hχc
  exact (weak_moment_localized_raw_trace_balance
    hLip hc hV hVc hκ hstrong hK hKc hpush hTl hTw B hχ hχc).2

end KLS
end

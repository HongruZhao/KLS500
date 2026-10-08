import KLS.WeakMomentLocalTraceTensor
import KLS.WeakMomentH1CutoffSequence
import KLS.RawWeakTraceDerivative
import KLS.RawTraceEnergyPassage
import KLS.WeakHessianTensorSymmetry
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

open MeasureTheory Set Filter Matrix
open scoped ContDiff Topology NNReal ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- Genuine weak tensor identities yield both tensor symmetries and hence
 positivity and comparison of the actual raw trace terms almost everywhere. -/
theorem weak_moment_rawTrace_nonneg_and_comparison
    {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : ContDiff ℝ 2 V) (hVc : ConvexOn ℝ univ V)
    {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun p => V p - (κ / 2) * ‖p‖ ^ 2))
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    {T : Space n → Fin n → Matrix (Fin n) (Fin n) ℝ}
    (hTl : ∀ k i j S, IsCompact S → MemLp (fun x => T x k i j) 2 (volume.restrict S))
    (hTw : ∀ k i j, HasLocalWeakCoordinateDerivative
      (fun x => coordinateHessian u x i j) (fun x => T x k i j) k)
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.PosSemidef) :
    ∀ᵐ x ∂potentialMeasure u,
      0 ≤ rawHessianTraceGradientTerm (coordinateHessian u x) B (T x) ∧
      0 ≤ rawHessianTraceTargetTerm (coordinateHessian u x) (coordinateHessian V (gradient u x)) B ∧
      0 ≤ rawHessianTraceThirdTerm (coordinateHessian u x) B (T x) ∧
      rawHessianTraceGradientTerm (coordinateHessian u x) B (T x) ≤
        rawHessianTraceThirdTerm (coordinateHessian u x) B (T x) := by
  have hG := weak_moment_gradient_lipschitz_of_uniformlyConvex_target
    hLip hc (hV.of_le (by norm_num)) hVc hκ hstrong hK hKc hpush
  have hAe := weak_moment_ae_hessian_equation_of_gradient_lipschitz hLip hc hV.continuous hK hKc hpush hG
  have hTs := actual_weak_third_tensor_ae_symmetric hLip.locallyLipschitz hG.locallyLipschitz hTl hTw
  have hac : potentialMeasure u ≪ volume := withDensity_absolutelyContinuous _ _
  filter_upwards [hAe.filter_mono hac.ae_le,hTs.filter_mono hac.ae_le] with x hx ht
  have hsym (i : Fin n) : (T x i).IsSymm := Matrix.IsSymm.ext (fun j k => (ht i j k).2.symm)
  obtain ⟨hA,hF,hD⟩ := rawHessianTrace_terms_nonneg hx.1
    (coordinateHessian_posSemidef_of_convex hV hVc (gradient u x)) hB (T x) hsym
  exact ⟨hA,hF,hD,rawHessianTrace_gradient_le_third hx.1 hB.isHermitian.isSymm (T x)
    (fun i j k => (ht i j k).1) (fun i j k => (ht i j k).2)⟩

end KLS
end

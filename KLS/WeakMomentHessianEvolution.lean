import KLS.WeakHessianEvolutionPotential
import KLS.WeakMomentThirdTensor
import KLS.WeakMomentInverseDivergence

open MeasureTheory Set Filter InnerProductSpace Matrix
open scoped ContDiff Topology ENNReal NNReal Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- Literal weak moment transport supplies bounded compact H1 Hessian
 evolution in the actual source measure. All source C1/C1,1, actual MA and
 weighted inverse-column hypotheses are derived from weak transport. -/
theorem weak_moment_hessian_evolution_bounded_H1
    {u V f : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : ContDiff ℝ 2 V) (hVc : ConvexOn ℝ univ V)
    {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun p => V p - (κ / 2) * ‖p‖ ^ 2))
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    {T : Space n → Fin n → Matrix (Fin n) (Fin n) ℝ} {F : Fin n → Space n → ℝ}
    (hTl : ∀ k i j S, IsCompact S → MemLp (fun x => T x k i j) 2 (volume.restrict S))
    (hTw : ∀ k i j, HasLocalWeakCoordinateDerivative
      (fun x => coordinateHessian u x i j) (fun x => T x k i j) k)
    (hf : ∀ S, IsCompact S → MemLp f 2 (volume.restrict S)) (hfc : HasCompactSupport f)
    {C : ℝ} (hbound : ∀ᵐ x, ‖f x‖ ≤ C)
    (hFl : ∀ a S, IsCompact S → MemLp (F a) 2 (volume.restrict S))
    (hFw : ∀ a, HasLocalWeakCoordinateDerivative f (F a) a) (k l : Fin n) :
    (∀ a, Integrable (fun x => ((coordinateHessian u x)⁻¹ * T x k) a l * F a x) (potentialMeasure u)) ∧
    Integrable (fun x =>
      (-coordinateHessian u x k l +
        (coordinateHessian u x * coordinateHessian V (gradient u x) * coordinateHessian u x) k l +
        ((coordinateHessian u x)⁻¹ * T x k * (coordinateHessian u x)⁻¹ * T x l).trace) * f x)
      (potentialMeasure u) ∧
    -(∑ a, ∫ x, ((coordinateHessian u x)⁻¹ * T x k) a l * F a x ∂potentialMeasure u) =
      ∫ x,
        (-coordinateHessian u x k l +
          (coordinateHessian u x * coordinateHessian V (gradient u x) * coordinateHessian u x) k l +
          ((coordinateHessian u x)⁻¹ * T x k * (coordinateHessian u x)⁻¹ * T x l).trace) * f x ∂potentialMeasure u := by
  have hV1 : ContDiff ℝ 1 V := hV.of_le (by norm_num)
  have hu := moment_contDiff_one_closedTarget hLip hc hV.continuous hK hKc hpush
  have hG := weak_moment_gradient_lipschitz_of_uniformlyConvex_target
    hLip hc hV1 hVc hκ hstrong hK hKc hpush
  have hAe := weak_moment_ae_hessian_equation_of_gradient_lipschitz
    hLip hc hV.continuous hK hKc hpush hG
  have hMA : ∀ᵐ x, (coordinateHessian u x).det = Real.exp (-u x + V (gradient u x)) :=
    hAe.mono fun _ hx => hx.2.1
  have hdiv (ψ : Space n → ℝ) (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) (i : Fin n) :
      (∑ a, ∫ x, Real.exp (-u x) * (coordinateHessian u x)⁻¹ a i * coordinateDerivative ψ a x) =
        ∫ x, Real.exp (-u x) * coordinateDerivative V i (gradient u x) * ψ x :=
    weak_moment_inverseHessian_integral_column_volume
      hLip hc hV1 hVc hκ hstrong hK hKc hpush hψ hψc i
  exact actual_weak_hessian_evolution_bounded_H1_potential
    hu hV hG hMA hTl hTw hdiv hf hfc hbound hFl hFw k l

end KLS
end

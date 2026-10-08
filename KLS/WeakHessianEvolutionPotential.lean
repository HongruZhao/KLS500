import KLS.WeakHessianEvolutionTests

open MeasureTheory Set Filter InnerProductSpace Matrix
open scoped ContDiff Topology ENNReal NNReal Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- The bounded compact H1 Hessian evolution uses the actual potential
measure, retaining all integrability conclusions for later energy tests. -/
theorem actual_weak_hessian_evolution_bounded_H1_potential
    {u V f : Space n → ℝ} {G : ℝ≥0}
    {T : Space n → Fin n → Matrix (Fin n) (Fin n) ℝ} {F : Fin n → Space n → ℝ}
    (hu : ContDiff ℝ 1 u) (hV : ContDiff ℝ 2 V) (hG : LipschitzWith G (gradient u))
    (hMA : ∀ᵐ x, (coordinateHessian u x).det = Real.exp (-u x + V (gradient u x)))
    (hTl : ∀ k i j S, IsCompact S → MemLp (fun x => T x k i j) 2 (volume.restrict S))
    (hTw : ∀ k i j, HasLocalWeakCoordinateDerivative
      (fun x => coordinateHessian u x i j) (fun x => T x k i j) k)
    (hdiv : ∀ ψ : Space n → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ → ∀ i,
      (∑ a, ∫ x, Real.exp (-u x) * (coordinateHessian u x)⁻¹ a i * coordinateDerivative ψ a x) =
        ∫ x, Real.exp (-u x) * coordinateDerivative V i (gradient u x) * ψ x)
    (hf : ∀ S, IsCompact S → MemLp f 2 (volume.restrict S)) (hc : HasCompactSupport f)
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
  have he := actual_weak_hessian_evolution_bounded_H1 hu hV hG hMA hTl hTw hdiv hf hc hbound hFl hFw k l
  refine ⟨?_, ?_, ?_⟩
  · intro a
    apply (integrable_potentialMeasure_iff hu.continuous.measurable).mpr
    simpa only [mul_assoc, mul_comm, mul_left_comm] using he.1 a
  · apply (integrable_potentialMeasure_iff hu.continuous.measurable).mpr
    simpa only [mul_assoc, mul_comm, mul_left_comm] using he.2.1
  · simpa only [integral_potentialMeasure hu.continuous.measurable, mul_assoc, mul_comm, mul_left_comm] using he.2.2

end KLS
end

import KLS.WeakMatrixInverse
import KLS.WeakMomentExponentialScalar

open MeasureTheory Set Filter InnerProductSpace Matrix
open scoped ContDiff Topology ENNReal NNReal Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- Actual Hessian entries of a locally Lipschitz gradient are locally bounded. -/
theorem memLp_top_actual_hessian_of_locallyLipschitz_gradient
    {u : Space n → ℝ} (hG : LocallyLipschitz (gradient u))
    (i j : Fin n) {S : Set (Space n)} (hS : IsCompact S) :
    MemLp (fun x => coordinateHessian u x i j) ∞ (volume.restrict S) :=
  memLp_top_coordinateDerivative_of_locallyLipschitz
    (locallyLipschitz_coordinateDerivative_of_gradient hG j) i hS

/-- The actual Monge–Ampère exponential supplies the reciprocal scalar in
 the polynomial inverse construction. Thus the actual inverse Hessian has
 the ordered weak derivative -J*T_k*J, with no inverse derivative premise. -/
theorem actual_mongeAmpere_inverse_hasLocalWeakDerivative
    {u V : Space n → ℝ} {G : ℝ≥0}
    {T : Space n → Fin n → Matrix (Fin n) (Fin n) ℝ}
    (hu : ContDiff ℝ 1 u) (hV : ContDiff ℝ 1 V) (hG : LipschitzWith G (gradient u))
    (hMA : ∀ᵐ x, (coordinateHessian u x).det = Real.exp (-u x + V (gradient u x)))
    (hTl : ∀ k i j S, IsCompact S → MemLp (fun x => T x k i j) 2 (volume.restrict S))
    (hTw : ∀ k i j, HasLocalWeakCoordinateDerivative
      (fun x => coordinateHessian u x i j) (fun x => T x k i j) k) :
    (∀ i j S, IsCompact S →
      MemLp (fun x => (coordinateHessian u x)⁻¹ i j) ∞ (volume.restrict S)) ∧
    (∀ k i j S, IsCompact S →
      MemLp (fun x => (-((coordinateHessian u x)⁻¹ * T x k * (coordinateHessian u x)⁻¹)) i j)
        2 (volume.restrict S)) ∧
    ∀ k i j, HasLocalWeakCoordinateDerivative (fun x => (coordinateHessian u x)⁻¹ i j)
      (fun x => (-((coordinateHessian u x)⁻¹ * T x k * (coordinateHessian u x)⁻¹)) i j) k := by
  have hr (k : Fin n) := weak_exp_scaled_momentExponent hu hV hG (-1) k
  have hrecip : ∀ᵐ x, Real.exp ((-1) * (-u x + V (gradient u x))) *
      (coordinateHessian u x).det = 1 := by
    filter_upwards [hMA] with x hx
    rw [hx, ← Real.exp_add]
    have he : (-1 : ℝ) * (-u x + V (gradient u x)) + (-u x + V (gradient u x)) = 0 := by ring
    rw [he, Real.exp_zero]
  have hinv (k : Fin n) := hasLocalWeakCoordinateDerivative_matrixInv_of_reciprocalDet
    (hTw k) (hr k).1
    (fun i j S hS => memLp_top_actual_hessian_of_locallyLipschitz_gradient hG.locallyLipschitz i j hS)
    (hTl k) (hr k).2.1 (memLp_two_on_compacts_of_top (hr k).2.2) hrecip
  refine ⟨?_, fun k => (hinv k).2.1, fun k => (hinv k).2.2⟩
  intro i j S hS
  exact (hinv i).1 i j S hS

end KLS
end

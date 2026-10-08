import KLS.WeightedL2TaylorTensor
import KLS.WeightedIterationTaylorRecursion

/-! Actual order-zero and order-one coefficients for the spectral mean-loss estimate. -/
open MeasureTheory InnerProductSpace Matrix
open scoped ContDiff RealInnerProductSpace Topology BigOperators
noncomputable section
namespace KLS
variable {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]

theorem exponentialTiltCoordinateTaylor_zero (f : Space n → ℝ) (a : Fin 0 → Fin n) :
    exponentialTiltCoordinateTaylor φ f 0 a = ∫ x, f x ∂potentialMeasure φ := by
  simp [exponentialTiltCoordinateTaylor, exponentialTiltTaylorCoefficient,
    iteratedFDeriv_zero_apply]

theorem weightedDiffusion_exponentialTiltCoordinateTaylor_one
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    {f : Space n → ℝ} (hf : ContDiff ℝ 2 f)
    (hL : MemLp (weightedDiffusion φ f) 2 (potentialMeasure φ))
    (hF : Integrable (fun x => ‖gradient f x‖ ^ 2) (potentialMeasure φ))
    (a : Fin 1 → Fin n) :
    exponentialTiltCoordinateTaylor φ (-weightedDiffusion φ f) 1 a =
      ∫ x, coordinateDerivative f (a 0) x ∂potentialMeasure φ := by
  have hd := hasFDerivAt_weightedDiffusion_exponentialTilt_zero hφ hκ hlower hf hL hF
  have hg : Integrable (gradient f) (potentialMeasure φ) :=
    (memLp_gradient_of_integrable_sq (hf.of_le (by norm_num)) hF).integrable (by norm_num)
  unfold exponentialTiltCoordinateTaylor exponentialTiltTaylorCoefficient
  rw [iteratedFDeriv_one_apply]
  simp only [Pi.neg_apply]
  rw [hd.fderiv]
  simp only [Nat.factorial_one, Nat.cast_one, div_one, innerSL_apply_apply,
    EuclideanSpace.inner_single_right, RCLike.conj_to_real, one_mul]
  have hi := (EuclideanSpace.proj (a 0) : Space n →L[ℝ] ℝ).integral_comp_comm hg
  change (∫ x, gradient f x (a 0) ∂potentialMeasure φ) =
    (∫ x, gradient f x ∂potentialMeasure φ) (a 0) at hi
  change (∫ x, gradient f x ∂potentialMeasure φ) (a 0) = _
  rw [← hi]
  exact integral_congr_ae (.of_forall fun x => (coordinateDerivative_eq_gradient f (a 0) x).symm)

end KLS
end
#print axioms KLS.exponentialTiltCoordinateTaylor_zero
#print axioms KLS.weightedDiffusion_exponentialTiltCoordinateTaylor_one

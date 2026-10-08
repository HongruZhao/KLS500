import KLS.WeightedTaylorLowOrder

/-! The order-one tilted coefficient is the actual first mixed moment for a centered observable. -/
open MeasureTheory InnerProductSpace Matrix
open scoped ContDiff RealInnerProductSpace Topology BigOperators
noncomputable section
namespace KLS
variable {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))

include hφ hκ hlower

theorem hasFDerivAt_exponentialTilt_average_zero_of_integral_eq_zero
    {f : Space n → ℝ} (hf : MemLp f 2 (potentialMeasure φ))
    (hmean : ∫ x, f x ∂potentialMeasure φ = 0) :
    HasFDerivAt (fun z => ∫ x, f x ∂exponentialTilt (potentialMeasure φ) z)
      (∑ i, (∫ x, f x * x i ∂potentialMeasure φ) •
        (EuclideanSpace.proj i : Space n →L[ℝ] ℝ)) 0 := by
  have hD := normExponentialDomain_of_memLp_potentialMeasure hφ hκ hlower hf
  have hD1 := normExponentialDomain_of_memLp_potentialMeasure hφ hκ hlower
    (memLp_const (μ := potentialMeasure φ) (p := 2) (1 : ℝ))
  have hN := hasFDerivAt_tiltNumerator_coordinate_of_normExponentialDomain hD 0
  have hZ := hasFDerivAt_tiltNumerator_coordinate_of_normExponentialDomain hD1 0
  have hz : tiltNumerator (potentialMeasure φ) (fun _ => 0) (fun _ => 1) 0 ≠ 0 := by
    simp [tiltNumerator]
  have hd := hN.mul ((hasDerivAt_inv hz).comp_hasFDerivAt 0 hZ)
  convert hd using 1
  · funext z
    change tiltAverage (potentialMeasure φ) (fun x => inner ℝ z x) f = _
    simp only [tiltAverage_eq_ratio, Pi.mul_apply, Function.comp_apply,
      tiltNumerator, tiltPartition, zero_add, one_mul, div_eq_mul_inv]
  · simp [tiltNumerator, hmean]

theorem exponentialTiltCoordinateTaylor_one_of_integral_eq_zero
    {f : Space n → ℝ} (hf : MemLp f 2 (potentialMeasure φ))
    (hmean : ∫ x, f x ∂potentialMeasure φ = 0) (a : Fin 1 → Fin n) :
    exponentialTiltCoordinateTaylor φ f 1 a = ∫ x, f x * x (a 0) ∂potentialMeasure φ := by
  have hd := hasFDerivAt_exponentialTilt_average_zero_of_integral_eq_zero hφ hκ hlower hf hmean
  unfold exponentialTiltCoordinateTaylor exponentialTiltTaylorCoefficient
  rw [iteratedFDeriv_one_apply, hd.fderiv]
  simp

end KLS
end
#print axioms KLS.hasFDerivAt_exponentialTilt_average_zero_of_integral_eq_zero
#print axioms KLS.exponentialTiltCoordinateTaylor_one_of_integral_eq_zero

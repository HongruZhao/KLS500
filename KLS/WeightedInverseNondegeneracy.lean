import KLS.TensorCenteredGradientInverse
import KLS.WeightedEnergyGraphClosability
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! Nondegeneracy of the actual Poisson inverse on actual centered L² forcing.
The proof uses its genuine compact-test equation, with no injectivity or
source-density assumption. -/

open MeasureTheory InnerProductSpace Matrix Filter
open scoped ContDiff RealInnerProductSpace ENNReal

noncomputable section
namespace KLS
variable {n : ℕ}

theorem weightedH1_eq_zero_of_gradient_eq_zero
    {φ : Space n → ℝ} {κ : ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    {U : WeightedCenteredH1 φ} (hU : weightedH1Gradient φ U = 0) : U = 0 := by
  have hg : (∑ i, ‖weightedH1Derivative φ i U‖ ^ 2) = 0 := by
    rw [← weightedH1Gradient_norm_sq, hU, norm_zero, zero_pow (by norm_num)]
  have hv := weightedH1_value_norm_sq_le_energy hφ hκ hlower U
  rw [hg, mul_zero] at hv
  have hv0 : weightedH1Value φ U = 0 := by
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (weightedH1Value φ U)]
  apply weightedH1Value_injective (hφ.of_le (by norm_num))
  simpa using hv0

/-- The actual compact-test equation detects every centered L² forcing. -/
theorem weightedEnergyInverse_eq_zero_iff_of_integral_eq_zero
    {φ : Space n → ℝ} {κ : ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (g : Lp ℝ 2 (potentialMeasure φ)) (hg : (∫ x, g x ∂potentialMeasure φ) = 0) :
    weightedEnergyInverse hφ hκ hlower g = 0 ↔ g = 0 := by
  constructor
  · intro hzero
    have hae : ∀ᵐ x ∂potentialMeasure φ, g x = 0 := by
      apply ae_eq_zero_of_integral_contDiff_smul_eq_zero
        ((Lp.memLp g).integrable (by norm_num)).locallyIntegrable
      intro ψ hψ hc
      have ht := weightedEnergyInverse_compact_test_of_integral_eq_zero
        hφ hκ hlower g hg (hψ.of_le (by simp)) hc
      rw [hzero] at ht
      have hi (i : Fin n) : (∫ x, (0 : Lp ℝ 2 (potentialMeasure φ)) x *
          coordinateDerivative ψ i x ∂potentialMeasure φ) = 0 := by
        apply integral_eq_zero_of_ae
        filter_upwards [Lp.coeFn_zero ℝ 2 (potentialMeasure φ)] with x hx
        change (0 : Lp ℝ 2 (potentialMeasure φ)) x * coordinateDerivative ψ i x = 0
        rw [hx]
        simp
      simp only [map_zero, hi, Finset.sum_const_zero] at ht
      simpa only [smul_eq_mul, mul_comm] using ht.symm
    apply Lp.ext
    filter_upwards [hae, Lp.coeFn_zero ℝ 2 (potentialMeasure φ)] with x hx hz
    exact hx.trans hz.symm
  · rintro rfl
    exact map_zero _

theorem weightedEnergyInverse_gradient_eq_zero_iff_of_integral_eq_zero
    {φ : Space n → ℝ} {κ : ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (g : Lp ℝ 2 (potentialMeasure φ)) (hg : (∫ x, g x ∂potentialMeasure φ) = 0) :
    weightedH1Gradient φ (weightedEnergyInverse hφ hκ hlower g) = 0 ↔ g = 0 := by
  constructor
  · intro hzero
    exact (weightedEnergyInverse_eq_zero_iff_of_integral_eq_zero hφ hκ hlower g hg).mp
      (weightedH1_eq_zero_of_gradient_eq_zero hφ hκ hlower hzero)
  · rintro rfl
    simp

end KLS
end

#print axioms KLS.weightedH1_eq_zero_of_gradient_eq_zero
#print axioms KLS.weightedEnergyInverse_eq_zero_iff_of_integral_eq_zero
#print axioms KLS.weightedEnergyInverse_gradient_eq_zero_iff_of_integral_eq_zero

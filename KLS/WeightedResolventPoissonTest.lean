import KLS.WeightedResolventWeakEquation
import KLS.WeightedPoissonRegularity

open MeasureTheory InnerProductSpace Set Filter Matrix
open scoped Topology ContDiff ENNReal RealInnerProductSpace

noncomputable section
namespace KLS
variable {n : ℕ} {φ : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure φ)]

/-- The actual centered resolvent satisfies the weighted Poisson identity with its
own value moved to the forcing. Neither a solution nor its weak equation is supplied. -/
theorem weightedResolvent_poisson_test (hφ : Continuous φ)
    {t : ℝ} (ht : 0 < t) (g : Lp ℝ 2 (potentialMeasure φ))
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ 3 ψ) (hc : HasCompactSupport ψ) :
    (∑ i : Fin n, ∫ x,
      weightedH1Derivative φ i (weightedResolventH1 φ ht g) x * coordinateDerivative ψ i x
        ∂potentialMeasure φ) =
      ∫ x, (t⁻¹ * (g x - (∫ y, g y ∂potentialMeasure φ) -
        weightedH1Value φ (weightedResolventH1 φ ht g) x)) * ψ x ∂potentialMeasure φ := by
  have hψ2 := memLp_of_continuous_hasCompactSupport hφ hψ.continuous hc
  obtain ⟨V, hV, hdV⟩ := exists_weightedH1_of_smoothCompact hφ hψ hc
  have he := weightedResolvent_variational φ ht g V
  rw [weighted_inner_centered_test hψ2 hV, weighted_inner_centered_test hψ2 hV,
    weightedResolvent_integral_eq_zero hφ ht g, zero_mul, sub_zero,
    weightedEnergyForm_eq_sum_integral] at he
  have hpair : (∑ i : Fin n, ∫ x,
      weightedH1Derivative φ i (weightedResolventH1 φ ht g) x * weightedH1Derivative φ i V x
        ∂potentialMeasure φ) =
      ∑ i : Fin n, ∫ x,
        weightedH1Derivative φ i (weightedResolventH1 φ ht g) x * coordinateDerivative ψ i x
          ∂potentialMeasure φ := by
    apply Finset.sum_congr rfl
    intro i _
    exact integral_congr_ae (EventuallyEq.rfl.fun_mul (hdV i))
  rw [hpair] at he
  have hgψ : Integrable (fun x => g x * ψ x) (potentialMeasure φ) :=
    (Lp.memLp g).integrable_mul hψ2
  have hmψ := (hψ2.integrable (by norm_num)).const_mul (∫ y, g y ∂potentialMeasure φ)
  have huψ : Integrable (fun x => weightedResolvent φ ht g x * ψ x) (potentialMeasure φ) :=
    (Lp.memLp (weightedResolvent φ ht g)).integrable_mul hψ2
  change _ = ∫ x, (t⁻¹ * (g x - (∫ y, g y ∂potentialMeasure φ) -
    weightedResolvent φ ht g x)) * ψ x ∂potentialMeasure φ
  simp_rw [mul_assoc, sub_mul]
  rw [integral_const_mul, integral_sub (f := fun x => g x * ψ x - (∫ y, g y ∂potentialMeasure φ) * ψ x) (g := fun x => weightedResolvent φ ht g x * ψ x) (hgψ.sub hmψ) huψ,
    integral_sub hgψ hmψ, integral_const_mul]
  apply (mul_left_cancel₀ ht.ne')
  rw [← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul]
  linarith

/-- For an actual L2 function the weak forcing uses the original function,
with its exact mean and the constructed solution value. -/
theorem weightedResolvent_poisson_test_toLp (hφ : Continuous φ)
    {t : ℝ} (ht : 0 < t) {g : Space n → ℝ} (hg : MemLp g 2 (potentialMeasure φ))
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ 3 ψ) (hc : HasCompactSupport ψ) :
    (∑ i : Fin n, ∫ x,
      weightedH1Derivative φ i (weightedResolventH1 φ ht (hg.toLp g)) x * coordinateDerivative ψ i x
        ∂potentialMeasure φ) =
      ∫ x, (t⁻¹ * (g x - (∫ y, g y ∂potentialMeasure φ) -
        weightedH1Value φ (weightedResolventH1 φ ht (hg.toLp g)) x)) * ψ x
          ∂potentialMeasure φ := by
  rw [weightedResolvent_poisson_test hφ ht (hg.toLp g) hψ hc]
  have hm := integral_congr_ae hg.coeFn_toLp
  apply integral_congr_ae
  filter_upwards [hg.coeFn_toLp] with x hx
  rw [hx, hm]

end KLS
end

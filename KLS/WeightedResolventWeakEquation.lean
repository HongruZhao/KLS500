import KLS.WeightedMassResolvent

open MeasureTheory InnerProductSpace Filter
open scoped RealInnerProductSpace NNReal

noncomputable section
namespace KLS
variable {n : ℕ} {φ : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure φ)]

/-- Convert the actual centered compact test pairing to ordinary integrals. -/
theorem weighted_inner_centered_test {ψ : Space n → ℝ}
    (hψ : MemLp ψ 2 (potentialMeasure φ))
    {V : Lp ℝ 2 (potentialMeasure φ)}
    (hV : (V : Space n → ℝ) =ᵐ[potentialMeasure φ]
      fun x => ψ x - ∫ y, ψ y ∂potentialMeasure φ)
    (g : Lp ℝ 2 (potentialMeasure φ)) :
    inner ℝ g V = (∫ x, g x * ψ x ∂potentialMeasure φ) -
      (∫ x, g x ∂potentialMeasure φ) * (∫ x, ψ x ∂potentialMeasure φ) := by
  rw [L2.inner_def]
  calc
    _ = ∫ x, g x * ψ x - g x * ∫ y, ψ y ∂potentialMeasure φ ∂potentialMeasure φ := by
      apply integral_congr_ae
      filter_upwards [hV] with x hx
      simp only [RCLike.inner_apply, conj_trivial, hx]
      ring
    _ = _ := by
      have hp : Integrable (fun x => g x * ψ x) (potentialMeasure φ) :=
        (Lp.memLp g).integrable_mul hψ
      have hm : Integrable (fun x => g x * (∫ y, ψ y ∂potentialMeasure φ))
          (potentialMeasure φ) := ((Lp.memLp g).integrable (by norm_num)).mul_const _
      rw [integral_sub hp hm, integral_mul_const]

/-- The constructed resolvent solves the actual shifted diffusion equation
against every compact C3 test, with its genuine H1 derivative coordinates. -/
theorem weightedMassResolvent_compact_test (hφ : Continuous φ)
    {t : ℝ} (ht : 0 < t) (g : Lp ℝ 2 (potentialMeasure φ))
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ 3 ψ) (hc : HasCompactSupport ψ) :
    (∫ x, weightedMassResolvent φ ht g x * ψ x ∂potentialMeasure φ) +
      t * (∑ i : Fin n, ∫ x,
        weightedH1Derivative φ i (weightedResolventH1 φ ht g) x *
          coordinateDerivative ψ i x ∂potentialMeasure φ) =
      ∫ x, g x * ψ x ∂potentialMeasure φ := by
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
  have hfull : (∫ x, weightedMassResolvent φ ht g x * ψ x ∂potentialMeasure φ) =
      (∫ x, g x ∂potentialMeasure φ) * (∫ x, ψ x ∂potentialMeasure φ) +
        ∫ x, weightedResolvent φ ht g x * ψ x ∂potentialMeasure φ := by
    calc
      _ = ∫ x, (∫ y, g y ∂potentialMeasure φ) * ψ x +
          weightedResolvent φ ht g x * ψ x ∂potentialMeasure φ := by
        apply integral_congr_ae
        filter_upwards [weightedMassResolvent_ae ht g] with x hx
        rw [hx, add_mul]
      _ = _ := by
        have hp : Integrable (fun x => weightedResolvent φ ht g x * ψ x)
            (potentialMeasure φ) := (Lp.memLp (weightedResolvent φ ht g)).integrable_mul hψ2
        have hm : Integrable (fun x => (∫ y, g y ∂potentialMeasure φ) * ψ x)
            (potentialMeasure φ) := (hψ2.integrable (by norm_num)).const_mul _
        rw [integral_add hm hp, integral_const_mul]
  rw [hfull]
  linarith

end KLS
end

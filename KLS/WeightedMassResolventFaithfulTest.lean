import KLS.WeightedMassResolventSmooth

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology ContDiff ENNReal RealInnerProductSpace

noncomputable section
namespace KLS
variable {n : ℕ} {φ : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure φ)]

/-- The actual full resolvent equation extends to every original faithful
finite-energy test, using that test's proved membership in the actual graph. -/
theorem weightedMassResolvent_faithful_test (hφ : Continuous φ)
    {t : ℝ} (ht : 0 < t) (g : Lp ℝ 2 (potentialMeasure φ))
    {ψ : Space n → ℝ} (hψ : LocallyLipschitzTests (potentialMeasure φ) ψ)
    (heψ : energy (potentialMeasure φ) ψ < ⊤) :
    (∫ x, weightedMassResolvent φ ht g x * ψ x ∂potentialMeasure φ) +
      t * (∑ i : Fin n, ∫ x,
        weightedH1Derivative φ i (weightedResolventH1 φ ht g) x *
          coordinateDerivative ψ i x ∂potentialMeasure φ) =
      ∫ x, g x * ψ x ∂potentialMeasure φ := by
  have hψ2 := hψ.2
  obtain ⟨V, hV, hdV⟩ := exists_weightedH1_of_faithful_test hφ hψ heψ
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

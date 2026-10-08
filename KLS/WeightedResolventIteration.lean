import KLS.WeightedResolventBounds

open MeasureTheory InnerProductSpace
open scoped RealInnerProductSpace NNReal

noncomputable section
namespace KLS
variable {n : ℕ}

/-- The constructed centered resolvent has actual mean zero. -/
theorem weightedResolvent_integral_eq_zero {φ : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)] (hφ : Continuous φ)
    {t : ℝ} (ht : 0 < t) (g : Lp ℝ 2 (potentialMeasure φ)) :
    (∫ x, weightedResolvent φ ht g x ∂potentialMeasure φ) = 0 :=
  weightedH1_integral_eq_zero hφ (weightedResolventH1 φ ht g)

/-- Spectral decay for actual finite iterates, with every dependence on the
Poincare constant and time step explicit. No semigroup is postulated. -/
theorem weightedResolvent_iterate_norm_le {φ : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)] (hφ : Continuous φ)
    {C : ℝ≥0} (hC : C ∈ poincareConstants (potentialMeasure φ))
    {t : ℝ} (ht : 0 < t) (k : ℕ) (g : Lp ℝ 2 (potentialMeasure φ)) :
    ‖(weightedResolvent φ ht)^[k] g‖ ≤ ((C : ℝ) / ((C : ℝ) + t)) ^ k * ‖g‖ := by
  have hq : 0 ≤ (C : ℝ) / ((C : ℝ) + t) := by positivity
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    calc
      _ ≤ ((C : ℝ) / ((C : ℝ) + t)) * ‖(weightedResolvent φ ht)^[k] g‖ :=
        weightedResolvent_norm_le_of_poincareConstant hφ hC ht _
      _ ≤ ((C : ℝ) / ((C : ℝ) + t)) *
          (((C : ℝ) / ((C : ℝ) + t)) ^ k * ‖g‖) := mul_le_mul_of_nonneg_left ih hq
      _ = _ := by rw [pow_succ]; ring

end KLS
end

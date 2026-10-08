import KLS.WeightedResolventConstruction
import KLS.WeightedOptimalPoincare

open MeasureTheory InnerProductSpace
open scoped RealInnerProductSpace NNReal

noncomputable section
namespace KLS
variable {n : ℕ}

theorem weightedResolvent_energy_nonneg (φ : Space n → ℝ) {t : ℝ} (ht : 0 < t)
    (g : Lp ℝ 2 (potentialMeasure φ)) :
    0 ≤ weightedEnergyForm φ (weightedResolventH1 φ ht g) (weightedResolventH1 φ ht g) := by
  rw [weightedEnergyForm_self]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Positivity as a Hilbert-space operator; this does not assert order preservation. -/
theorem weightedResolvent_pairing_nonneg (φ : Space n → ℝ) {t : ℝ} (ht : 0 < t)
    (g : Lp ℝ 2 (potentialMeasure φ)) : 0 ≤ inner ℝ g (weightedResolvent φ ht g) := by
  rw [← weightedResolvent_energy_identity]
  exact add_nonneg (sq_nonneg _) (mul_nonneg ht.le (weightedResolvent_energy_nonneg φ ht g))

/-- The actual value operator is an L2 contraction for every positive time. -/
theorem weightedResolvent_norm_le (φ : Space n → ℝ) {t : ℝ} (ht : 0 < t)
    (g : Lp ℝ 2 (potentialMeasure φ)) : ‖weightedResolvent φ ht g‖ ≤ ‖g‖ := by
  have he := weightedResolvent_energy_identity φ ht g
  have hp := mul_nonneg ht.le (weightedResolvent_energy_nonneg φ ht g)
  have hi := real_inner_le_norm g (weightedResolvent φ ht g)
  nlinarith [norm_nonneg g, norm_nonneg (weightedResolvent φ ht g)]

/-- Testing the actual variational equation bounds the genuine derivative energy. -/
theorem weightedResolvent_energy_le (φ : Space n → ℝ) {t : ℝ} (ht : 0 < t)
    (g : Lp ℝ 2 (potentialMeasure φ)) :
    t * weightedEnergyForm φ (weightedResolventH1 φ ht g) (weightedResolventH1 φ ht g) ≤
      ‖g‖ ^ 2 / 4 := by
  have he := weightedResolvent_energy_identity φ ht g
  have hi := real_inner_le_norm g (weightedResolvent φ ht g)
  nlinarith [sq_nonneg (2 * ‖weightedResolvent φ ht g‖ - ‖g‖)]

/-- A faithful Poincare constant gives the sharp resolvent L2 contraction factor.
The bound is proved for the constructed solution, rather than supplied as an operator axiom. -/
theorem weightedResolvent_norm_le_of_poincareConstant {φ : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)] (hφ : Continuous φ)
    {C : ℝ≥0} (hC : C ∈ poincareConstants (potentialMeasure φ))
    {t : ℝ} (ht : 0 < t) (g : Lp ℝ 2 (potentialMeasure φ)) :
    ‖weightedResolvent φ ht g‖ ≤ ((C : ℝ) / ((C : ℝ) + t)) * ‖g‖ := by
  have hp := weightedH1_bound_of_poincareConstant hφ hC (weightedResolventH1 φ ht g)
  change ‖weightedResolvent φ ht g‖ ^ 2 ≤ (C : ℝ) *
    weightedEnergyForm φ (weightedResolventH1 φ ht g) (weightedResolventH1 φ ht g) at hp
  have he := weightedResolvent_energy_identity φ ht g
  have hi := real_inner_le_norm g (weightedResolvent φ ht g)
  have hpt := mul_le_mul_of_nonneg_left hp ht.le
  have hci := mul_le_mul_of_nonneg_left hi C.property
  have hec := congrArg (fun z : ℝ => (C : ℝ) * z) he
  have hden : 0 < (C : ℝ) + t := add_pos_of_nonneg_of_pos C.property ht
  have hb : ((C : ℝ) + t) * ‖weightedResolvent φ ht g‖ ^ 2 ≤
      (C : ℝ) * ‖g‖ * ‖weightedResolvent φ ht g‖ := by nlinarith
  by_cases hz : ‖weightedResolvent φ ht g‖ = 0
  · rw [hz]
    positivity
  · have hr : 0 < ‖weightedResolvent φ ht g‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    have hlin : ((C : ℝ) + t) * ‖weightedResolvent φ ht g‖ ≤ (C : ℝ) * ‖g‖ := by
      apply (mul_le_mul_iff_right₀ hr).mp
      nlinarith [hb]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hden).mpr
    nlinarith [hlin]

end KLS
end

import KLS.WeightedOptimalPoincare
import KLS.WeightedEnergyInverse

/-! The actual weighted Poisson inverse has the sharp first-eigenvalue
norm and energy bounds. The eigenvalue is obtained from the actual compact
energy inclusion and agrees with the faithful Poincare constant. -/

open MeasureTheory InnerProductSpace Matrix
open scoped ContDiff RealInnerProductSpace ENNReal

noncomputable section
namespace KLS
variable {n : ℕ}

theorem weightedEnergyInverse_value_norm_le_of_rayleigh
    {φ : Space n → ℝ} {κ lam : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (hlam : 0 < lam)
    (hRay : ∀ V : WeightedCenteredH1 φ,
      lam * ‖weightedH1Value φ V‖ ^ 2 ≤ weightedEnergyForm φ V V)
    (g : Lp ℝ 2 (potentialMeasure φ)) :
    ‖weightedH1Value φ (weightedEnergyInverse hφ hκ hlower g)‖ ≤ lam⁻¹ * ‖g‖ := by
  let U := weightedEnergyInverse hφ hκ hlower g
  have hP := hRay U
  have hE := weightedEnergyInverse_variational hφ hκ hlower g U
  change weightedEnergyForm φ U U = inner ℝ g (weightedH1Value φ U) at hE
  rw [hE] at hP
  have hb := mul_le_mul_of_nonneg_left
    (hP.trans (real_inner_le_norm g (weightedH1Value φ U))) (inv_nonneg.mpr hlam.le)
  rw [← mul_assoc, inv_mul_cancel₀ hlam.ne', one_mul] at hb
  change ‖weightedH1Value φ U‖ ≤ lam⁻¹ * ‖g‖
  by_cases hz : ‖weightedH1Value φ U‖ = 0
  · rw [hz]
    positivity
  · have hp : 0 < ‖weightedH1Value φ U‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    apply le_of_mul_le_mul_right (b := ‖weightedH1Value φ U‖) ?_ hp
    nlinarith

theorem weightedEnergyInverse_energy_le_of_rayleigh
    {φ : Space n → ℝ} {κ lam : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (hlam : 0 < lam)
    (hRay : ∀ V : WeightedCenteredH1 φ,
      lam * ‖weightedH1Value φ V‖ ^ 2 ≤ weightedEnergyForm φ V V)
    (g : Lp ℝ 2 (potentialMeasure φ)) :
    (∑ i : Fin n, ‖weightedH1Derivative φ i
      (weightedEnergyInverse hφ hκ hlower g)‖ ^ 2) ≤ lam⁻¹ * ‖g‖ ^ 2 := by
  rw [weightedEnergyInverse_energy_identity]
  calc
    _ ≤ ‖g‖ * ‖weightedH1Value φ (weightedEnergyInverse hφ hκ hlower g)‖ :=
      real_inner_le_norm _ _
    _ ≤ ‖g‖ * (lam⁻¹ * ‖g‖) := mul_le_mul_of_nonneg_left
      (weightedEnergyInverse_value_norm_le_of_rayleigh hφ hκ hlower hlam hRay g)
      (norm_nonneg g)
    _ = _ := by ring

/-- The sharp inverse bounds hold for an eigenvalue whose reciprocal is the
actual optimal Poincare constant; no dimension-free estimate is assumed. -/
theorem exists_optimal_weightedEnergyInverse_bounds
    {φ : Space n → ℝ} {κ : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hn : 0 < n) (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a)) :
    ∃ lam : ℝ, 0 < lam ∧
      poincareConstant (potentialMeasure φ) = ENNReal.ofReal lam⁻¹ ∧
      ∀ g : Lp ℝ 2 (potentialMeasure φ),
        ‖weightedH1Value φ (weightedEnergyInverse hφ hκ hlower g)‖ ≤ lam⁻¹ * ‖g‖ ∧
        (∑ i : Fin n, ‖weightedH1Derivative φ i
          (weightedEnergyInverse hφ hκ hlower g)‖ ^ 2) ≤ lam⁻¹ * ‖g‖ ^ 2 := by
  obtain ⟨lam, U, _, hlam, hU, hweak, hmin, hCP⟩ :=
    exists_positive_weighted_eigenpair_with_optimal_poincare hn hφ hκ hlower
  have he : weightedEnergyForm φ U U = lam := by
    simpa only [real_inner_self_eq_norm_sq, hU, one_pow, mul_one] using hweak U
  have hm : ∀ V : WeightedCenteredH1 φ, ‖weightedH1Value φ V‖ = 1 →
      weightedEnergyForm φ U U ≤ weightedEnergyForm φ V V := by rwa [he]
  have hRay (V : WeightedCenteredH1 φ) :
      lam * ‖weightedH1Value φ V‖ ^ 2 ≤ weightedEnergyForm φ V V := by
    simpa only [he] using weightedRayleigh_minimizer_lower_bound hm V
  exact ⟨lam, hlam, hCP, fun g =>
    ⟨weightedEnergyInverse_value_norm_le_of_rayleigh hφ hκ hlower hlam hRay g,
      weightedEnergyInverse_energy_le_of_rayleigh hφ hκ hlower hlam hRay g⟩⟩

end KLS
end

#print axioms KLS.weightedEnergyInverse_value_norm_le_of_rayleigh
#print axioms KLS.weightedEnergyInverse_energy_le_of_rayleigh
#print axioms KLS.exists_optimal_weightedEnergyInverse_bounds

import KLS.WeightedFamilyEnergy

/-! The actual BKL normalized successor on finite families in the weighted
energy graph. A zero centered gradient produces scale and successor zero.
Otherwise the denominator is proved positive from the true inverse equation. -/

open MeasureTheory InnerProductSpace Matrix
open scoped ContDiff RealInnerProductSpace ENNReal

noncomputable section
namespace KLS
variable {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))

/-- The literal ratio in BKL (31), defined as zero when its numerator is zero. -/
def weightedSuccessorScale {ι : Type*} [Fintype ι] (U : WeightedH1Family φ ι) : ℝ :=
  ‖weightedFamilyCenteredGradient φ ι U‖ /
    ‖weightedFamilyGradient φ (Fin n × ι)
      (weightedFamilyEnergyInverse hφ hκ hlower (Fin n × ι)
        (weightedFamilyCenteredGradient φ ι U))‖

/-- Apply the actual inverse componentwise to the actual centered gradient,
then multiply by the actual normalizing ratio. -/
def weightedNormalizedSuccessor {ι : Type*} [Fintype ι] (U : WeightedH1Family φ ι) :
    WeightedH1Family φ (Fin n × ι) :=
  weightedSuccessorScale hφ hκ hlower U •
    weightedFamilyEnergyInverse hφ hκ hlower (Fin n × ι) (weightedFamilyCenteredGradient φ ι U)

theorem weightedSuccessor_denominator_eq_zero_iff {ι : Type*} [Fintype ι]
    (U : WeightedH1Family φ ι) :
    ‖weightedFamilyGradient φ (Fin n × ι)
      (weightedFamilyEnergyInverse hφ hκ hlower (Fin n × ι)
        (weightedFamilyCenteredGradient φ ι U))‖ = 0 ↔
      weightedFamilyCenteredGradient φ ι U = 0 := by
  rw [norm_eq_zero]
  exact weightedFamilyEnergyInverse_gradient_eq_zero_iff hφ hκ hlower _
    (weightedFamilyCenteredGradient_integral_eq_zero φ U)

theorem weightedSuccessorScale_nonneg {ι : Type*} [Fintype ι]
    (U : WeightedH1Family φ ι) : 0 ≤ weightedSuccessorScale hφ hκ hlower U :=
  div_nonneg (norm_nonneg _) (norm_nonneg _)

theorem weightedSuccessorScale_eq_zero {ι : Type*} [Fintype ι]
    (U : WeightedH1Family φ ι) (hzero : weightedFamilyCenteredGradient φ ι U = 0) :
    weightedSuccessorScale hφ hκ hlower U = 0 := by
  simp [weightedSuccessorScale, hzero]

theorem weightedNormalizedSuccessor_eq_zero {ι : Type*} [Fintype ι]
    (U : WeightedH1Family φ ι) (hzero : weightedFamilyCenteredGradient φ ι U = 0) :
    weightedNormalizedSuccessor hφ hκ hlower U = 0 := by
  simp [weightedNormalizedSuccessor, hzero]

theorem weightedSuccessorScale_pos {ι : Type*} [Fintype ι]
    (U : WeightedH1Family φ ι) (hne : weightedFamilyCenteredGradient φ ι U ≠ 0) :
    0 < weightedSuccessorScale hφ hκ hlower U := by
  apply div_pos (norm_pos_iff.mpr hne)
  exact lt_of_le_of_ne (norm_nonneg _)
    (Ne.symm (fun h => hne ((weightedSuccessor_denominator_eq_zero_iff hφ hκ hlower U).mp h)))

/-- Actual normalization preserves exactly the centered-gradient energy, BKL (33). -/
theorem weightedNormalizedSuccessor_gradient_norm {ι : Type*} [Fintype ι]
    (U : WeightedH1Family φ ι) :
    ‖weightedFamilyGradient φ (Fin n × ι) (weightedNormalizedSuccessor hφ hκ hlower U)‖ =
      ‖weightedFamilyCenteredGradient φ ι U‖ := by
  by_cases hz : weightedFamilyCenteredGradient φ ι U = 0
  · rw [weightedNormalizedSuccessor_eq_zero hφ hκ hlower U hz, map_zero, hz]
    simp
  · have hd : ‖weightedFamilyGradient φ (Fin n × ι)
        (weightedFamilyEnergyInverse hφ hκ hlower (Fin n × ι)
          (weightedFamilyCenteredGradient φ ι U))‖ ≠ 0 :=
      fun h => hz ((weightedSuccessor_denominator_eq_zero_iff hφ hκ hlower U).mp h)
    rw [weightedNormalizedSuccessor, map_smul, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (weightedSuccessorScale_nonneg hφ hκ hlower U), weightedSuccessorScale]
    exact div_mul_cancel₀ _ hd

/-- The exact one-step loss is the squared norm of the actual gradient mean, BKL (35). -/
theorem weightedNormalizedSuccessor_energy_defect {ι : Type*} [Fintype ι]
    (U : WeightedH1Family φ ι) :
    ‖weightedFamilyGradient φ ι U‖ ^ 2 -
      ‖weightedFamilyGradient φ (Fin n × ι) (weightedNormalizedSuccessor hφ hκ hlower U)‖ ^ 2 =
        ∑ ji : Fin n × ι, (∫ x, weightedFamilyGradient φ ι U ji x ∂potentialMeasure φ) ^ 2 := by
  rw [weightedNormalizedSuccessor_gradient_norm]
  have h := weightedFamilyCenteredGradient_norm_sq φ U
  linarith

theorem weightedNormalizedSuccessor_gradient_norm_le {ι : Type*} [Fintype ι]
    (U : WeightedH1Family φ ι) :
    ‖weightedFamilyGradient φ (Fin n × ι) (weightedNormalizedSuccessor hφ hκ hlower U)‖ ≤
      ‖weightedFamilyGradient φ ι U‖ := by
  rw [weightedNormalizedSuccessor_gradient_norm]
  exact weightedFamilyCenteredGradient_norm_le φ U

/-- The true inverse energy estimate forces the actual nonzero scale above sqrt(lam). -/
theorem weightedSuccessorScale_sq_ge_of_inverse_energy
    {lam : ℝ} (hlam : 0 < lam)
    (hb : ∀ f : Lp ℝ 2 (potentialMeasure φ),
      (∑ j, ‖weightedH1Derivative φ j (weightedEnergyInverse hφ hκ hlower f)‖ ^ 2) ≤ lam⁻¹ * ‖f‖ ^ 2)
    {ι : Type*} [Fintype ι] (U : WeightedH1Family φ ι)
    (hne : weightedFamilyCenteredGradient φ ι U ≠ 0) :
    lam ≤ (weightedSuccessorScale hφ hκ hlower U) ^ 2 := by
  let d := ‖weightedFamilyGradient φ (Fin n × ι)
    (weightedFamilyEnergyInverse hφ hκ hlower (Fin n × ι)
      (weightedFamilyCenteredGradient φ ι U))‖
  have hd : 0 < d := lt_of_le_of_ne (norm_nonneg _)
    (Ne.symm (fun h => hne ((weightedSuccessor_denominator_eq_zero_iff hφ hκ hlower U).mp h)))
  have he := weightedFamilyEnergyInverse_gradient_norm_sq_le hφ hκ hlower hb
    (weightedFamilyCenteredGradient φ ι U)
  change d ^ 2 ≤ lam⁻¹ * ‖weightedFamilyCenteredGradient φ ι U‖ ^ 2 at he
  have hm := mul_le_mul_of_nonneg_left he hlam.le
  rw [← mul_assoc, mul_inv_cancel₀ hlam.ne', one_mul] at hm
  have ha : (weightedSuccessorScale hφ hκ hlower U) ^ 2 * d ^ 2 =
      ‖weightedFamilyCenteredGradient φ ι U‖ ^ 2 := by
    change (‖weightedFamilyCenteredGradient φ ι U‖ / d) ^ 2 * d ^ 2 = _
    field_simp
  rw [← ha] at hm
  exact le_of_mul_le_mul_right hm (sq_pos_of_pos hd)

/-- The same attained eigenvalue controls every nonzero successor scale, at
every finite tensor rank. No scale bound or recursion is assumed. -/
theorem exists_optimal_weightedSuccessorScale_lower_bound (hn : 0 < n) :
    ∃ lam : ℝ, 0 < lam ∧
      poincareConstant (potentialMeasure φ) = ENNReal.ofReal lam⁻¹ ∧
      ∀ (ι : Type*) [Fintype ι] (U : WeightedH1Family φ ι),
        weightedFamilyCenteredGradient φ ι U ≠ 0 →
          lam ≤ (weightedSuccessorScale hφ hκ hlower U) ^ 2 := by
  obtain ⟨lam, hlam, hCP, hb⟩ := exists_optimal_weightedEnergyInverse_bounds hn hφ hκ hlower
  exact ⟨lam, hlam, hCP, fun ι _ U hne =>
    weightedSuccessorScale_sq_ge_of_inverse_energy hφ hκ hlower hlam (fun g => (hb g).2) U hne⟩

end KLS
end

#print axioms KLS.weightedSuccessor_denominator_eq_zero_iff
#print axioms KLS.weightedNormalizedSuccessor_gradient_norm
#print axioms KLS.weightedNormalizedSuccessor_energy_defect
#print axioms KLS.exists_optimal_weightedSuccessorScale_lower_bound

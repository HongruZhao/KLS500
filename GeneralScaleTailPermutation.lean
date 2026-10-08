import KLS.WeightedSuccessorPermutation

open MeasureTheory InnerProductSpace Matrix
open scoped ContDiff RealInnerProductSpace ENNReal BigOperators
noncomputable section
namespace KLS.ConstantReduction
variable {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))

theorem weightedNormalizedSuccessor_tail_permutation_norm_sq_le_generalScale
    {lam M : ℝ} (hlam : 0 < lam)
    (hb : ∀ g : Lp ℝ 2 (potentialMeasure φ),
      (∑ j, ‖weightedH1Derivative φ j (weightedEnergyInverse hφ hκ hlower g)‖ ^ 2) ≤
        lam⁻¹ * ‖g‖ ^ 2)
    {ι : Type*} [Fintype ι] (U : WeightedH1Family φ ι)
    (e : Equiv.Perm (Fin n × ι))
    (hscale : (weightedSuccessorScale hφ hκ hlower U) ^ 2 ≤ M * lam) :
    ‖weightedFamilyCenteredGradient φ (Fin n × ι) (weightedNormalizedSuccessor hφ hκ hlower U) -
      finiteL2Reindex (Equiv.prodCongr (Equiv.refl (Fin n)) e)
        (weightedFamilyCenteredGradient φ (Fin n × ι)
          (weightedNormalizedSuccessor hφ hκ hlower U))‖ ^ 2 ≤
        M * ‖weightedFamilyCenteredGradient φ ι U -
          finiteL2Reindex e (weightedFamilyCenteredGradient φ ι U)‖ ^ 2 := by
  rw [weightedNormalizedSuccessor_tail_permutation_identity, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs]
  have h := weightedTensorCenteredGradientInverse_norm_sq_le hφ hκ hlower hb
    (weightedFamilyCenteredGradient φ ι U - finiteL2Reindex e (weightedFamilyCenteredGradient φ ι U))
  calc
    _ ≤ (weightedSuccessorScale hφ hκ hlower U) ^ 2 *
        (lam⁻¹ * ‖weightedFamilyCenteredGradient φ ι U -
          finiteL2Reindex e (weightedFamilyCenteredGradient φ ι U)‖ ^ 2) :=
      mul_le_mul_of_nonneg_left h (sq_nonneg _)
    _ ≤ (M * lam) * (lam⁻¹ * ‖weightedFamilyCenteredGradient φ ι U -
        finiteL2Reindex e (weightedFamilyCenteredGradient φ ι U)‖ ^ 2) :=
      mul_le_mul_of_nonneg_right hscale (mul_nonneg (inv_nonneg.mpr hlam.le) (sq_nonneg _))
    _ = _ := by rw [← mul_assoc, mul_assoc M lam, mul_inv_cancel₀ hlam.ne', mul_one]

end KLS.ConstantReduction
end

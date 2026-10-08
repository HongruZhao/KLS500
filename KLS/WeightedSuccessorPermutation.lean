import KLS.FiniteL2Reindex
import KLS.WeightedSuccessorSymmetry

/-! The literal normalized successor commutes with permutations of its old
tensor indices. The attained inverse energy bound propagates each such
permutation defect; Hessian symmetry controls the new first swap. -/

open MeasureTheory InnerProductSpace Matrix
open scoped ContDiff RealInnerProductSpace ENNReal

noncomputable section
namespace KLS
variable {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))

theorem weightedFamilyCenteredGradient_inverse_eq {ι : Type*} [Fintype ι]
    (g : CenteredL2.Family (potentialMeasure φ) ι) :
    weightedFamilyCenteredGradient φ ι (weightedFamilyEnergyInverse hφ hκ hlower ι g) =
      weightedTensorCenteredGradientInverse hφ hκ hlower ι g := by
  apply PiLp.ext
  rintro ⟨j, i⟩
  simp only [weightedFamilyCenteredGradient_apply, weightedFamilyEnergyInverse_apply,
    weightedTensorCenteredGradientInverse, finiteL2VectorLift_apply,
    weightedCenteredGradientInverse_apply]

theorem weightedNormalizedSuccessor_centeredGradient_eq {ι : Type*} [Fintype ι]
    (U : WeightedH1Family φ ι) :
    weightedFamilyCenteredGradient φ (Fin n × ι) (weightedNormalizedSuccessor hφ hκ hlower U) =
      weightedSuccessorScale hφ hκ hlower U •
        weightedTensorCenteredGradientInverse hφ hκ hlower (Fin n × ι)
          (weightedFamilyCenteredGradient φ ι U) := by
  rw [weightedNormalizedSuccessor, map_smul, weightedFamilyCenteredGradient_inverse_eq]

theorem weightedTensorCenteredGradientInverse_norm_sq_le {ι : Type*} [Fintype ι] {C : ℝ}
    (hb : ∀ g : Lp ℝ 2 (potentialMeasure φ),
      (∑ j, ‖weightedH1Derivative φ j (weightedEnergyInverse hφ hκ hlower g)‖ ^ 2) ≤ C * ‖g‖ ^ 2)
    (g : CenteredL2.Family (potentialMeasure φ) ι) :
    ‖weightedTensorCenteredGradientInverse hφ hκ hlower ι g‖ ^ 2 ≤ C * ‖g‖ ^ 2 := by
  rw [← weightedFamilyCenteredGradient_inverse_eq]
  exact ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
    (weightedFamilyCenteredGradient_norm_le φ _)).trans
      (weightedFamilyEnergyInverse_gradient_norm_sq_le hφ hκ hlower hb g)

/-- BKL (42), for every genuine permutation of the older tensor indices. -/
theorem weightedNormalizedSuccessor_tail_permutation_identity
    {ι : Type*} [Fintype ι] (U : WeightedH1Family φ ι)
    (e : Equiv.Perm (Fin n × ι)) :
    weightedFamilyCenteredGradient φ (Fin n × ι) (weightedNormalizedSuccessor hφ hκ hlower U) -
      finiteL2Reindex (Equiv.prodCongr (Equiv.refl (Fin n)) e)
        (weightedFamilyCenteredGradient φ (Fin n × ι)
          (weightedNormalizedSuccessor hφ hκ hlower U)) =
      weightedSuccessorScale hφ hκ hlower U •
        weightedTensorCenteredGradientInverse hφ hκ hlower (Fin n × ι)
          (weightedFamilyCenteredGradient φ ι U - finiteL2Reindex e
            (weightedFamilyCenteredGradient φ ι U)) := by
  rw [weightedNormalizedSuccessor_centeredGradient_eq, map_smul, ← smul_sub, map_sub]
  rw [weightedTensorCenteredGradientInverse, finiteL2VectorLift_reindex]

/-- When the actual next scale is at most sqrt(2 lam), old-index permutation
defects grow by at most a factor two in squared L² norm. -/
theorem weightedNormalizedSuccessor_tail_permutation_norm_sq_le
    {lam : ℝ} (hlam : 0 < lam)
    (hb : ∀ g : Lp ℝ 2 (potentialMeasure φ),
      (∑ j, ‖weightedH1Derivative φ j (weightedEnergyInverse hφ hκ hlower g)‖ ^ 2) ≤
        lam⁻¹ * ‖g‖ ^ 2)
    {ι : Type*} [Fintype ι] (U : WeightedH1Family φ ι)
    (e : Equiv.Perm (Fin n × ι))
    (hscale : (weightedSuccessorScale hφ hκ hlower U) ^ 2 ≤ 2 * lam) :
    ‖weightedFamilyCenteredGradient φ (Fin n × ι) (weightedNormalizedSuccessor hφ hκ hlower U) -
      finiteL2Reindex (Equiv.prodCongr (Equiv.refl (Fin n)) e)
        (weightedFamilyCenteredGradient φ (Fin n × ι)
          (weightedNormalizedSuccessor hφ hκ hlower U))‖ ^ 2 ≤
        2 * ‖weightedFamilyCenteredGradient φ ι U -
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
    _ ≤ (2 * lam) * (lam⁻¹ * ‖weightedFamilyCenteredGradient φ ι U -
        finiteL2Reindex e (weightedFamilyCenteredGradient φ ι U)‖ ^ 2) :=
      mul_le_mul_of_nonneg_right hscale (mul_nonneg (inv_nonneg.mpr hlam.le) (sq_nonneg _))
    _ = _ := by rw [← mul_assoc, mul_assoc (2 : ℝ) lam, mul_inv_cancel₀ hlam.ne', mul_one]

/-- Hessian symmetry controls the actual first-index transposition. -/
theorem weightedNormalizedSuccessor_firstSwap_norm_sq_le
    {lam : ℝ} (hlam : 0 < lam) {ι : Type*} [Fintype ι]
    (U : WeightedH1Family φ ι) (W : WeightedH1Family φ (Fin n × ι))
    (f : ι → Space n → ℝ) (hf : ∀ i, ContDiff ℝ 2 (f i))
    (hd : ∀ j k i, (weightedH1Derivative φ j (W (k, i)) : Space n → ℝ)
      =ᵐ[potentialMeasure φ] fun x => coordinateHessian (f i) x j k)
    (hscale : weightedFamilyCenteredGradient φ ι U ≠ 0 →
      lam ≤ (weightedSuccessorScale hφ hκ hlower U) ^ 2) :
    ‖weightedFamilyCenteredGradient φ (Fin n × ι) (weightedNormalizedSuccessor hφ hκ hlower U) -
      finiteL2Reindex (tensorFirstSwapEquiv (Fin n) ι)
        (weightedFamilyCenteredGradient φ (Fin n × ι)
          (weightedNormalizedSuccessor hφ hκ hlower U))‖ ^ 2 ≤
        4 * weightedSuccessorHessianDefect hφ hκ hlower U W / lam := by
  obtain ⟨T, hT, hb⟩ := exists_weightedSuccessor_symmetric_approximation
    hφ hκ hlower hlam U W f hf hd hscale
  calc
    _ ≤ 4 * ‖weightedFamilyCenteredGradient φ (Fin n × ι)
        (weightedNormalizedSuccessor hφ hκ hlower U) - T‖ ^ 2 :=
      norm_sub_isometry_apply_sq_le _ _ T (finiteL2Reindex_firstSwap_fixed T hT)
    _ ≤ 4 * (weightedSuccessorHessianDefect hφ hκ hlower U W / lam) := by
      exact mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = _ := by ring

end KLS
end

#print axioms KLS.weightedNormalizedSuccessor_tail_permutation_identity
#print axioms KLS.weightedNormalizedSuccessor_tail_permutation_norm_sq_le
#print axioms KLS.weightedNormalizedSuccessor_firstSwap_norm_sq_le

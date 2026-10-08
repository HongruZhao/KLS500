import KLS.WeightedTaylorBlockSymmetry
import KLS.FiniteAveragePerturbation

/-! Actual Taylor-family perturbation and recovery. The only Taylor growth
premise is the previously named scalar criterion bound. -/

open MeasureTheory Matrix
open scoped ContDiff RealInnerProductSpace Topology BigOperators
noncomputable section
namespace KLS
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {φ : Space n → ℝ} {κ : ℝ} {ι : Type*} [Fintype ι]
  [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))

include hφ hκ hlower

theorem weightedL2BlockTaylor_sub (r d q : ℕ)
    (g h : CenteredL2.Family (potentialMeasure φ) (Fin n × WeightedIterationIndex n ι (r + q))) :
    weightedL2BlockTaylor φ r d q (g - h) =
      weightedL2BlockTaylor φ r d q g - weightedL2BlockTaylor φ r d q h := by
  unfold weightedL2BlockTaylor
  rw [weightedL2TaylorTensor_sub hφ hκ hlower, map_sub]

theorem weightedL2BlockTaylor_sub_norm_sq_le {R : ℝ} (hR : WeightedCoordinateTaylorBound φ R)
    (r d q : ℕ) (hd : 1 ≤ d)
    (g h : CenteredL2.Family (potentialMeasure φ) (Fin n × WeightedIterationIndex n ι (r + q))) :
    ‖weightedL2BlockTaylor φ r d q g - weightedL2BlockTaylor φ r d q h‖ ^ 2 ≤
      R ^ (2 * d) * ‖g - h‖ ^ 2 := by
  rw [← weightedL2BlockTaylor_sub hφ hκ hlower, norm_weightedL2BlockTaylor]
  exact weightedL2TaylorTensor_norm_sq_le hR hd (g - h)

/-- The original actual Taylor tensor is bounded by its first-2d average
and the actual L2 error of symmetrizing the original derivative indices. -/
theorem weightedL2TaylorTensor_norm_sq_le_partial_and_error
    {R : ℝ} (hR : WeightedCoordinateTaylorBound φ R)
    (r d q : ℕ) (hd : 1 ≤ d) (hq : q + 1 = 2 * d)
    (g : CenteredL2.Family (potentialMeasure φ) (Fin n × WeightedIterationIndex n ι (r + q))) :
    ‖weightedL2TaylorTensor φ d g‖ ^ 2 ≤
      2 * (16 : ℝ) ^ d * ‖finiteIsometryAverage
        (realTensorPrefixAction n (d + q + 1) (WeightedIterationIndex n ι r) (by omega : 2 * d ≤ d + q + 1))
        (weightedL2BlockTaylor φ r d q g)‖ ^ 2 +
      8 * (16 : ℝ) ^ d * R ^ (2 * d) * ‖g - finiteIsometryAverage
        (weightedGradientPermutationAction (potentialMeasure φ) n ι r q) g‖ ^ 2 := by
  let ρ := realTensorPrefixAction n (d + q + 1) (WeightedIterationIndex n ι r) (by omega : 2 * d ≤ d + q + 1)
  let S := finiteIsometryAverage (weightedGradientPermutationAction (potentialMeasure φ) n ι r q) g
  have hc : (1 : ℝ) ≤ 4 ^ d := one_le_pow₀ (by norm_num)
  have hy := norm_weightedL2BlockTaylor_symmetrized_le hφ hκ hlower r d q hq g
  have hrec := norm_sq_le_of_near_average_recovery ρ
    (weightedL2BlockTaylor φ r d q g) (weightedL2BlockTaylor φ r d q S) hc hy
  have he : ((4 : ℝ) ^ d) ^ 2 = 16 ^ d := by rw [← pow_mul, Nat.mul_comm d 2, pow_mul]; norm_num
  rw [norm_weightedL2BlockTaylor, he] at hrec
  have hdiff := weightedL2BlockTaylor_sub_norm_sq_le hφ hκ hlower hR r d q hd g S
  calc
    _ ≤ 2 * (16 : ℝ) ^ d * ‖finiteIsometryAverage ρ (weightedL2BlockTaylor φ r d q g)‖ ^ 2 +
        8 * (16 : ℝ) ^ d * ‖weightedL2BlockTaylor φ r d q g - weightedL2BlockTaylor φ r d q S‖ ^ 2 := hrec
    _ ≤ 2 * (16 : ℝ) ^ d * ‖finiteIsometryAverage ρ (weightedL2BlockTaylor φ r d q g)‖ ^ 2 +
        8 * (16 : ℝ) ^ d * (R ^ (2 * d) * ‖g - S‖ ^ 2) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hdiff (by positivity))
    _ = _ := by ring

theorem weightedL2BlockTaylor_iteration (U : WeightedH1Family φ ι) (r d q : ℕ) :
    weightedL2BlockTaylor φ r d q
      (weightedFamilyCenteredGradient φ (WeightedIterationIndex n ι (r + q))
        (weightedSuccessorIterate hφ hκ hlower U (r + q))) =
      weightedIterationBlockTaylor hφ hκ hlower U r d q (d + q) rfl := by
  exact (weightedIterationBlockTaylor_eq_reindex hφ hκ hlower U r d q (d + q) rfl).symm

end KLS
end

#print axioms KLS.weightedL2BlockTaylor_sub_norm_sq_le
#print axioms KLS.weightedL2TaylorTensor_norm_sq_le_partial_and_error
#print axioms KLS.weightedL2BlockTaylor_iteration

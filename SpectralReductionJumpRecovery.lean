import SpectralReductionJumpPrefix

open MeasureTheory Matrix
open scoped ContDiff RealInnerProductSpace Topology BigOperators
noncomputable section
namespace KLS.ConstantReduction
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {φ : Space n → ℝ} {ι : Type*} [Fintype ι]
  {κ : ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))

include hφ hκ hlower

theorem weightedL2TaylorTensor_norm_sq_le_partial_and_error_jumpYoung
    {β : ℕ → ℝ} (hβ : WeightedCoordinateTaylorCoefficientBound φ β)
    {ε : ℝ} (hε : 0 < ε)
    (r d k q : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) (hq : d + k ≤ q + 1)
    (g : CenteredL2.Family (potentialMeasure φ) (Fin n × WeightedIterationIndex n ι (r + q))) :
    ‖weightedL2TaylorTensor φ d g‖ ^ 2 ≤
      (1 + ε) * jumpRecoverySquared d k (q+1) * ‖finiteIsometryAverage
        (realTensorPrefixAction n (d + q + 1) (WeightedIterationIndex n ι r) (by omega : d + k ≤ d + q + 1))
        (weightedL2BlockTaylor φ r d q g)‖ ^ 2 +
      (jumpRecoverySquared d k (q+1) + (jumpRecoverySquared d k (q+1) - 1)/ε) * β d * ‖g - finiteIsometryAverage
        (weightedGradientPermutationAction (potentialMeasure φ) n ι r q) g‖ ^ 2 := by
  let ρ := realTensorPrefixAction n (d + q + 1) (WeightedIterationIndex n ι r) (by omega : d + k ≤ d + q + 1)
  let S := finiteIsometryAverage (weightedGradientPermutationAction (potentialMeasure φ) n ι r q) g
  have hc := jumpRecoverySquared_gt_one hd hk hq
  have hcsub : 0 ≤ jumpRecoverySquared d k (q+1)-1 := by linarith
  have hy := norm_sq_weightedL2BlockTaylor_symmetrized_jump_le hφ hκ hlower r d k q hq g
  have horth : inner ℝ (weightedL2BlockTaylor φ r d q g) (weightedL2BlockTaylor φ r d q S) =
      ‖weightedL2BlockTaylor φ r d q S‖^2 := by
    change inner ℝ (weightedL2BlockTaylor φ r d q g)
      (weightedL2BlockTaylor φ r d q (finiteIsometryAverage _ g)) = _
    rw [weightedL2BlockTaylor_suffix_average hφ hκ hlower]
    exact inner_finiteIsometryAverage_self _ _
  have hrec := norm_sq_le_of_projection_recovery_coefficient ρ
    (weightedL2BlockTaylor φ r d q g) (weightedL2BlockTaylor φ r d q S) hc hε hy horth
  rw [norm_weightedL2BlockTaylor] at hrec
  have hdiff := weightedL2BlockTaylor_sub_norm_sq_le_coefficient hφ hκ hlower hβ r d q hd g S
  calc
    _ ≤ (1 + ε) * jumpRecoverySquared d k (q+1) * ‖finiteIsometryAverage ρ (weightedL2BlockTaylor φ r d q g)‖ ^ 2 +
        (jumpRecoverySquared d k (q+1) + (jumpRecoverySquared d k (q+1) - 1)/ε) * ‖weightedL2BlockTaylor φ r d q g - weightedL2BlockTaylor φ r d q S‖ ^ 2 := hrec
    _ ≤ (1 + ε) * jumpRecoverySquared d k (q+1) * ‖finiteIsometryAverage ρ (weightedL2BlockTaylor φ r d q g)‖ ^ 2 +
        (jumpRecoverySquared d k (q+1) + (jumpRecoverySquared d k (q+1) - 1)/ε) * (β d * ‖g - S‖ ^ 2) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hdiff (by positivity))
    _ = _ := by ring


end KLS.ConstantReduction
end

import SpectralReductionExactRecovery
import KLS.WeightedIterationTaylorEnergy

/-! Coefficient-sequence Taylor bounds preserve the rank-dependent size of
actual coordinate Taylor operators instead of replacing every rank by R^(2d). -/

open MeasureTheory Matrix
open scoped ContDiff RealInnerProductSpace Topology BigOperators
noncomputable section
namespace KLS.ConstantReduction
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {φ : Space n → ℝ}

/-- Squared full-L2 coordinate Taylor bounds, with the actual coefficient of
each rank kept separately. -/
def WeightedCoordinateTaylorCoefficientBound (φ : Space n → ℝ) (β : ℕ → ℝ) : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∀ f : Lp ℝ 2 (potentialMeasure φ),
    (∑ a : Fin d → Fin n, exponentialTiltCoordinateTaylor φ f d a ^ 2) ≤ β d * ‖f‖ ^ 2

theorem weightedL2TaylorTensor_norm_sq_le_coefficient {β : ℕ → ℝ}
    (hβ : WeightedCoordinateTaylorCoefficientBound φ β) {d : ℕ} (hd : 1 ≤ d)
    {ι : Type*} [Fintype ι] (g : CenteredL2.Family (potentialMeasure φ) ι) :
    ‖weightedL2TaylorTensor φ d g‖ ^ 2 ≤ β d * ‖g‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type,
    Finset.sum_comm, Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => hβ d hd (g i))

variable {κ : ℝ} {ι : Type*} [Fintype ι]
  [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))

include hφ hκ hlower

theorem weightedL2BlockTaylor_sub_norm_sq_le_coefficient {β : ℕ → ℝ} (hβ : WeightedCoordinateTaylorCoefficientBound φ β)
    (r d q : ℕ) (hd : 1 ≤ d)
    (g h : CenteredL2.Family (potentialMeasure φ) (Fin n × WeightedIterationIndex n ι (r + q))) :
    ‖weightedL2BlockTaylor φ r d q g - weightedL2BlockTaylor φ r d q h‖ ^ 2 ≤
      β d * ‖g - h‖ ^ 2 := by
  rw [← weightedL2BlockTaylor_sub hφ hκ hlower, norm_weightedL2BlockTaylor]
  exact weightedL2TaylorTensor_norm_sq_le_coefficient hβ hd (g - h)

theorem weightedL2TaylorTensor_norm_sq_le_partial_and_error_coefficient
    {β : ℕ → ℝ} (hβ : WeightedCoordinateTaylorCoefficientBound φ β)
    (r d q : ℕ) (hd : 1 ≤ d) (hq : q + 1 = 2 * d)
    (g : CenteredL2.Family (potentialMeasure φ) (Fin n × WeightedIterationIndex n ι (r + q))) :
    ‖weightedL2TaylorTensor φ d g‖ ^ 2 ≤
      2 * ((2 * d).choose d : ℝ) ^ 2 * ‖finiteIsometryAverage
        (realTensorPrefixAction n (d + q + 1) (WeightedIterationIndex n ι r) (by omega : 2 * d ≤ d + q + 1))
        (weightedL2BlockTaylor φ r d q g)‖ ^ 2 +
      2 * (1 + ((2 * d).choose d : ℝ)) ^ 2 * β d * ‖g - finiteIsometryAverage
        (weightedGradientPermutationAction (potentialMeasure φ) n ι r q) g‖ ^ 2 := by
  let ρ := realTensorPrefixAction n (d + q + 1) (WeightedIterationIndex n ι r) (by omega : 2 * d ≤ d + q + 1)
  let S := finiteIsometryAverage (weightedGradientPermutationAction (potentialMeasure φ) n ι r q) g
  have hc : (0 : ℝ) ≤ ((2 * d).choose d : ℝ) := Nat.cast_nonneg _
  have hy := norm_weightedL2BlockTaylor_symmetrized_choose_le hφ hκ hlower r d q hq g
  have hrec := norm_sq_le_of_near_average_recovery_exact ρ
    (weightedL2BlockTaylor φ r d q g) (weightedL2BlockTaylor φ r d q S) hc hy
  rw [norm_weightedL2BlockTaylor] at hrec
  have hdiff := weightedL2BlockTaylor_sub_norm_sq_le_coefficient hφ hκ hlower hβ r d q hd g S
  calc
    _ ≤ 2 * ((2 * d).choose d : ℝ) ^ 2 * ‖finiteIsometryAverage ρ (weightedL2BlockTaylor φ r d q g)‖ ^ 2 +
        2 * (1 + ((2 * d).choose d : ℝ)) ^ 2 * ‖weightedL2BlockTaylor φ r d q g - weightedL2BlockTaylor φ r d q S‖ ^ 2 := hrec
    _ ≤ 2 * ((2 * d).choose d : ℝ) ^ 2 * ‖finiteIsometryAverage ρ (weightedL2BlockTaylor φ r d q g)‖ ^ 2 +
        2 * (1 + ((2 * d).choose d : ℝ)) ^ 2 * (β d * ‖g - S‖ ^ 2) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hdiff (by positivity))
    _ = _ := by ring



variable (U : WeightedH1Family φ ι)

theorem weightedIterationTaylorEnergy_le_next_coefficient {β : ℕ → ℝ} (hβ : WeightedCoordinateTaylorCoefficientBound φ β)
    {d : ℕ} (hd : 1 ≤ d) (k : ℕ) :
    weightedIterationTaylorEnergy hφ hκ hlower U d k ≤
      β d * weightedIterationEnergy hφ hκ hlower U (k + 1) := by
  have hn := congrArg (fun t : ℝ => t ^ 2)
    (weightedNormalizedSuccessor_gradient_norm hφ hκ hlower (weightedSuccessorIterate hφ hκ hlower U k))
  have he : weightedIterationEnergy hφ hκ hlower U (k + 1) =
      ‖weightedFamilyCenteredGradient φ (WeightedIterationIndex n ι k)
        (weightedSuccessorIterate hφ hκ hlower U k)‖ ^ 2 := hn
  rw [he]
  exact weightedL2TaylorTensor_norm_sq_le_coefficient hβ hd _

theorem weightedIterationTaylorEnergy_le_initial_coefficient {lam : ℝ} {β : ℕ → ℝ}
    (hβ : WeightedCoordinateTaylorCoefficientBound φ β) (hβ0 : ∀ d, 0 ≤ β d)
    (hE0 : weightedIterationEnergy hφ hκ hlower U 0 = lam)
    {d : ℕ} (hd : 1 ≤ d) (k : ℕ) :
    weightedIterationTaylorEnergy hφ hκ hlower U d k ≤ lam * β d := by
  have he := weightedIterationEnergy_antitone hφ hκ hlower U (Nat.zero_le (k + 1))
  rw [hE0] at he
  have hRpow : 0 ≤ β d := hβ0 d
  exact (weightedIterationTaylorEnergy_le_next_coefficient hφ hκ hlower U hβ hd k).trans
    ((mul_le_mul_of_nonneg_left he hRpow).trans_eq (mul_comm _ _))

end KLS.ConstantReduction
end

#print axioms KLS.ConstantReduction.weightedL2TaylorTensor_norm_sq_le_coefficient
#print axioms KLS.ConstantReduction.weightedL2TaylorTensor_norm_sq_le_partial_and_error_coefficient
#print axioms KLS.ConstantReduction.weightedIterationTaylorEnergy_le_initial_coefficient

import KLS.WeightedEigenMeanLoss

/-! BKL Lemma 3.9 for the genuine orbit and its actual stopping index. -/
open MeasureTheory InnerProductSpace Matrix
open scoped ContDiff RealInnerProductSpace Topology BigOperators
noncomputable section
namespace KLS.ConstantReduction
variable {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
  (U : WeightedCenteredH1 φ)
  (F : (k : ℕ) → WeightedIterationIndex n (Fin 1) k → Space n → ℝ)
  (hF : ∀ k i, ContDiff ℝ (⊤ : ℕ∞) (F k i))
  (hV : ∀ k i, F k i =ᵐ[volume] (weightedH1Value φ
    (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower (weightedSingleFamily U) k i) : Space n → ℝ))
  (hL : ∀ k i, MemLp (weightedDiffusion φ (F k i)) 2 (potentialMeasure φ))
  {lam : ℝ} (hU : ‖weightedH1Value φ U‖ = 1)
  (heigen : ∀ x, weightedDiffusion φ (F 0 (0 : Fin 1)) x = -lam * F 0 (0 : Fin 1) x)
  (hsecond : ∀ v : Space n, (∫ x, inner ℝ v x ^ 2 ∂potentialMeasure φ) ≤ ‖v‖ ^ 2)

include hF hV hL hU heigen hsecond

/-- The index convention starts at zero. This is exactly the paper's finite
mean-loss bound, with actual order-one Taylor tensors of the centered gradients. -/
theorem weightedIteration_sum_meanLoss_le_generalScale {M : ℝ} (N : ℕ)
    (hscale : ∀ k < N, (weightedSuccessorScale (hφ.of_le (by simp)) hκ hlower
      (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower (weightedSingleFamily U) k)) ^ 2 ≤ M * lam) :
    (∑ k ∈ Finset.range (N + 1),
      weightedIterationMeanLoss (hφ.of_le (by simp)) hκ hlower (weightedSingleFamily U) k) ≤
      lam ^ 2 + M * lam * ∑ k ∈ Finset.range N,
        ‖weightedL2TaylorTensor φ 1 (weightedFamilyCenteredGradient φ
          (WeightedIterationIndex n (Fin 1) k)
          (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower (weightedSingleFamily U) k))‖ ^ 2 := by
  have hp0 := weightedEigenIteration_initial_meanLoss_le (hφ.of_le (by simp)) hκ hlower U
    ((hF 0 (0 : Fin 1)).of_le (by simp)) (hV 0 (0 : Fin 1)) hU heigen hsecond
  rw [Finset.sum_range_succ', add_comm]
  apply add_le_add hp0
  calc
    _ = ∑ k ∈ Finset.range N,
        (weightedSuccessorScale (hφ.of_le (by simp)) hκ hlower
          (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower (weightedSingleFamily U) k)) ^ 2 *
        ‖weightedL2TaylorTensor φ 1 (weightedFamilyCenteredGradient φ
          (WeightedIterationIndex n (Fin 1) k)
          (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower (weightedSingleFamily U) k))‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro k _
      exact weightedIterationMeanLoss_succ_eq_scale_taylor hφ hκ hlower
        (weightedSingleFamily U) F hF hV hL k
    _ ≤ ∑ k ∈ Finset.range N, M * lam *
        ‖weightedL2TaylorTensor φ 1 (weightedFamilyCenteredGradient φ
          (WeightedIterationIndex n (Fin 1) k)
          (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower (weightedSingleFamily U) k))‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_right (hscale k (Finset.mem_range.mp hk)) (sq_nonneg _)
    _ = _ := (Finset.mul_sum _ _ _).symm

end KLS.ConstantReduction
end

#print axioms KLS.ConstantReduction.weightedIteration_sum_meanLoss_le_generalScale

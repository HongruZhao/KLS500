import SpectralReductionJumpRecovery
import SpectralReductionGeneralPartial
import WeightedTaylorSymmetrization

/-! Exact BKL Lemma 3.8 recovery coefficients and a generic proved
symmetrization coefficient interface, retaining the genuine
partial Taylor recursion, literal block symmetry, and the proved gradient
symmetrization estimate on the same weighted iteration. -/

open MeasureTheory Matrix
open scoped ContDiff RealInnerProductSpace Topology BigOperators
noncomputable section
namespace KLS.ConstantReduction
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
  {ι : Type*} [Fintype ι] (U : WeightedH1Family φ ι)
  (F : (k : ℕ) → WeightedIterationIndex n ι k → Space n → ℝ)
  (W : (k : ℕ) → WeightedH1Family φ (Fin n × WeightedIterationIndex n ι k))
  (hF : ∀ k i, ContDiff ℝ (⊤ : ℕ∞) (F k i))
  (hV : ∀ k i, F k i =ᵐ[volume] (weightedH1Value φ
    (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U k i) : Space n → ℝ))
  (hL : ∀ k i, MemLp (weightedDiffusion φ (F k i)) 2 (potentialMeasure φ))
  (hW : ∀ k j l i, (weightedH1Derivative φ j (W k (l, i)) : Space n → ℝ)
    =ᵐ[potentialMeasure φ] fun x => coordinateHessian (F k i) x j l)

include hF hV hL

theorem weightedIteration_taylor_jumpYoung
    {lam M η ε : ℝ} (hε : 0 < ε) {β : ℕ → ℝ}
    (hβ : WeightedCoordinateTaylorCoefficientBound φ β) (hβ0 : ∀ d, 0 ≤ β d)
    (r d k s : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) (hs : d ≤ s + 1) (w : Fin (s+k) → ℝ)
    (hscale : ∀ l, r ≤ l → l < r + (s + k) →
      (weightedSuccessorScale (hφ.of_le (by simp)) hκ hlower
        (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U l)) ^ 2 ≤ M * lam)
    (hsym : ‖weightedFamilyCenteredGradient φ (WeightedIterationIndex n ι (r + (s + k)))
        (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U (r + (s + k))) -
      weightedIterationSymmetrizedGradient (hφ.of_le (by simp)) hκ hlower U r (s + k)‖ ^ 2 ≤
        η / lam * ∑ i : Fin (s + k), w i * weightedIterationDefect hφ hκ hlower U W (r + i)) :
    ‖weightedL2TaylorTensor φ d
      (weightedFamilyCenteredGradient φ (WeightedIterationIndex n ι (r + (s + k)))
        (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U (r + (s + k))))‖ ^ 2 ≤
      (1 + ε) * jumpRecoverySquared d k (s+k+1) * (M * lam) ^ k *
        ‖weightedL2TaylorTensor φ (d + k)
          (weightedFamilyCenteredGradient φ (WeightedIterationIndex n ι (r + s))
            (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U (r + s)))‖ ^ 2 +
      ((jumpRecoverySquared d k (s+k+1)+(jumpRecoverySquared d k (s+k+1)-1)/ε) * η) * β d / lam *
        ∑ i : Fin (s + k), w i * weightedIterationDefect hφ hκ hlower U W (r + i) := by
  have hc := jumpRecoverySquared_gt_one hd hk (by omega : d + k ≤ s + k + 1)
  have hcsub : 0≤jumpRecoverySquared d k (s+k+1)-1 := by linarith
  let g := weightedFamilyCenteredGradient φ (WeightedIterationIndex n ι (r + (s + k)))
    (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U (r + (s + k)))
  have hrec := weightedL2TaylorTensor_norm_sq_le_partial_and_error_jumpYoung (hφ.of_le (by simp)) hκ hlower
    hβ hε r d k (s + k) hd hk (by omega) g
  have he := weightedL2BlockTaylor_iteration (hφ.of_le (by simp)) hκ hlower U r d (s + k)
  change weightedL2BlockTaylor φ r d (s + k) g = _ at he
  rw [he] at hrec
  have hp := weightedIterationBlockTaylor_partial_norm_sq_le_of_scale hφ hκ hlower U F hF hV hL
    r d s k (d + k) (d + (s + k)) (by omega) (by omega) (by omega)
      (fun j hj => hscale (r + s + j) (by omega) (by omega))
  have hg := hsym
  change ‖g - finiteIsometryAverage (weightedGradientPermutationAction (potentialMeasure φ) n ι r (s + k)) g‖ ^ 2 ≤ _ at hg
  have hRpow : 0 ≤ β d := hβ0 d
  calc
    _ ≤ (1 + ε) * jumpRecoverySquared d k (s+k+1) * ‖finiteIsometryAverage
        (realTensorPrefixAction n (d + (s + k) + 1) (WeightedIterationIndex n ι r) (by omega : d + k ≤ d + (s + k) + 1))
        (weightedIterationBlockTaylor (hφ.of_le (by simp)) hκ hlower U r d (s + k) (d + (s + k)) rfl)‖ ^ 2 +
      (jumpRecoverySquared d k (s+k+1)+(jumpRecoverySquared d k (s+k+1)-1)/ε) * β d * ‖g - finiteIsometryAverage
        (weightedGradientPermutationAction (potentialMeasure φ) n ι r (s + k)) g‖ ^ 2 := hrec
    _ ≤ (1 + ε) * jumpRecoverySquared d k (s+k+1) * ((M * lam) ^ k *
        ‖weightedL2TaylorTensor φ (d + k)
          (weightedFamilyCenteredGradient φ (WeightedIterationIndex n ι (r + s))
            (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U (r + s)))‖ ^ 2) +
      (jumpRecoverySquared d k (s+k+1)+(jumpRecoverySquared d k (s+k+1)-1)/ε) * β d * (η / lam *
        ∑ i : Fin (s + k), w i * weightedIterationDefect hφ hκ hlower U W (r + i)) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hp (by positivity))
        (mul_le_mul_of_nonneg_left hg (mul_nonneg (by positivity) hRpow))
    _ = _ := by ring

end KLS.ConstantReduction
end


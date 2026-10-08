import KLS.WeightedTaylorBlockRecovery
import KLS.WeightedIterationSymmetrization

/-! Actual BKL Lemma 3.8 with explicit coefficients, combining genuine
partial Taylor recursion, literal block symmetry, and the proved gradient
symmetrization estimate on the same weighted iteration. -/

open MeasureTheory Matrix
open scoped ContDiff RealInnerProductSpace Topology BigOperators
noncomputable section
namespace KLS
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

include hF hV hL hW

/-- With s+1=d, the current actual iteration level is r+2d−1 and the earlier
level is r+d−1. These are paper indices i and i−d, respectively. -/
theorem weightedIteration_taylor_doubling_explicit
    {lam R : ℝ} (hlam : 0 < lam)
    (hb : ∀ g : Lp ℝ 2 (potentialMeasure φ),
      (∑ j, ‖weightedH1Derivative φ j (weightedEnergyInverse (hφ.of_le (by simp)) hκ hlower g)‖ ^ 2) ≤
        lam⁻¹ * ‖g‖ ^ 2)
    (hR : WeightedCoordinateTaylorBound φ R)
    (r d s : ℕ) (hd : 1 ≤ d) (hs : s + 1 = d)
    (hscale : ∀ k, r ≤ k → k < r + (s + d) →
      (weightedSuccessorScale (hφ.of_le (by simp)) hκ hlower
        (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U k)) ^ 2 ≤ 2 * lam) :
    ‖weightedL2TaylorTensor φ d
      (weightedFamilyCenteredGradient φ (WeightedIterationIndex n ι (r + (s + d)))
        (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U (r + (s + d))))‖ ^ 2 ≤
      2 * (16 : ℝ) ^ d * (2 * lam) ^ d *
        ‖weightedL2TaylorTensor φ (2 * d)
          (weightedFamilyCenteredGradient φ (WeightedIterationIndex n ι (r + s))
            (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U (r + s)))‖ ^ 2 +
      (8 * (16 : ℝ) ^ d * (128 : ℝ) ^ (2 * d)) * R ^ (2 * d) / lam *
        ∑ i : Fin (s + d), weightedIterationDefect hφ hκ hlower U W (r + i) := by
  let g := weightedFamilyCenteredGradient φ (WeightedIterationIndex n ι (r + (s + d)))
    (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U (r + (s + d)))
  have hq : s + d + 1 = 2 * d := by omega
  have hrec := weightedL2TaylorTensor_norm_sq_le_partial_and_error (hφ.of_le (by simp)) hκ hlower
    hR r d (s + d) hd hq g
  have he := weightedL2BlockTaylor_iteration (hφ.of_le (by simp)) hκ hlower U r d (s + d)
  change weightedL2BlockTaylor φ r d (s + d) g = _ at he
  rw [he] at hrec
  have hp := weightedIterationBlockTaylor_partial_norm_sq_le hφ hκ hlower U F hF hV hL
    r d s d (2 * d) (d + (s + d)) (by omega) (by omega) (by omega)
      (fun j hj => hscale (r + s + j) (by omega) (by omega))
  have hg := weightedIteration_symmetrization_bound (hφ.of_le (by simp)) hκ hlower hφ hlam hb
    U F W (fun k i => (hF k i).of_le (by simp)) hW r (s + d)
      (fun k hk hkj => hscale k (by omega) hkj)
  change ‖g - finiteIsometryAverage (weightedGradientPermutationAction (potentialMeasure φ) n ι r (s + d)) g‖ ^ 2 ≤ _ at hg
  conv at hg => rhs; rw [hq]
  have hRpow : 0 ≤ R ^ (2 * d) := by rw [pow_mul]; exact pow_nonneg (sq_nonneg R) d
  calc
    _ ≤ 2 * (16 : ℝ) ^ d * ‖finiteIsometryAverage
        (realTensorPrefixAction n (d + (s + d) + 1) (WeightedIterationIndex n ι r) (by omega : 2 * d ≤ d + (s + d) + 1))
        (weightedIterationBlockTaylor (hφ.of_le (by simp)) hκ hlower U r d (s + d) (d + (s + d)) rfl)‖ ^ 2 +
      8 * (16 : ℝ) ^ d * R ^ (2 * d) * ‖g - finiteIsometryAverage
        (weightedGradientPermutationAction (potentialMeasure φ) n ι r (s + d)) g‖ ^ 2 := hrec
    _ ≤ 2 * (16 : ℝ) ^ d * ((2 * lam) ^ d *
        ‖weightedL2TaylorTensor φ (2 * d)
          (weightedFamilyCenteredGradient φ (WeightedIterationIndex n ι (r + s))
            (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U (r + s)))‖ ^ 2) +
      8 * (16 : ℝ) ^ d * R ^ (2 * d) * ((128 : ℝ) ^ (2 * d) / lam *
        ∑ i : Fin (s + d), weightedIterationDefect hφ hκ hlower U W (r + i)) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hp (by positivity))
        (mul_le_mul_of_nonneg_left hg (mul_nonneg (by positivity) hRpow))
    _ = _ := by ring

end KLS
end

#print axioms KLS.weightedIteration_taylor_doubling_explicit

import GeneralScaleTailPermutation
import KLS.WeightedIterationAdjacentSwap

open MeasureTheory InnerProductSpace Matrix
open scoped ContDiff RealInnerProductSpace ENNReal BigOperators
noncomputable section
namespace KLS.ConstantReduction
variable {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))

theorem weightedIterationSwapDefect_succ_le_generalScale
    {lam M : ℝ} (hlam : 0 < lam)
    (hb : ∀ g : Lp ℝ 2 (potentialMeasure φ),
      (∑ j, ‖weightedH1Derivative φ j (weightedEnergyInverse hφ hκ hlower g)‖ ^ 2) ≤
        lam⁻¹ * ‖g‖ ^ 2)
    {ι : Type*} [Fintype ι] (U : WeightedH1Family φ ι) (k l : ℕ)
    (hscale : (weightedSuccessorScale hφ hκ hlower (weightedSuccessorIterate hφ hκ hlower U k)) ^ 2
      ≤ M * lam) :
    weightedIterationSwapDefect hφ hκ hlower U (k + 1) (l + 1) ≤
      M * weightedIterationSwapDefect hφ hκ hlower U k l := by
  exact weightedNormalizedSuccessor_tail_permutation_norm_sq_le_generalScale hφ hκ hlower hlam hb
    (weightedSuccessorIterate hφ hκ hlower U k) (weightedGradientAdjacentSwap n ι k l) hscale

/-- Propagate an actual first-swap defect through l actual successors. -/
theorem weightedIterationSwapDefect_propagation_generalScale
    {lam M : ℝ} (hlam : 0 < lam) (hM : 1 ≤ M)
    (hb : ∀ g : Lp ℝ 2 (potentialMeasure φ),
      (∑ j, ‖weightedH1Derivative φ j (weightedEnergyInverse hφ hκ hlower g)‖ ^ 2) ≤
        lam⁻¹ * ‖g‖ ^ 2)
    {ι : Type*} [Fintype ι] (U : WeightedH1Family φ ι) (r l : ℕ)
    (hscale : ∀ k, r + 1 ≤ k → k < r + 1 + l →
      (weightedSuccessorScale hφ hκ hlower (weightedSuccessorIterate hφ hκ hlower U k)) ^ 2 ≤ M * lam) :
    weightedIterationSwapDefect hφ hκ hlower U (r + 1 + l) l ≤
      M ^ l * weightedIterationSwapDefect hφ hκ hlower U (r + 1) 0 := by
  induction l with
  | zero => simp
  | succ l ih =>
    have hi := ih (fun k hk hk' => hscale k hk (by omega))
    have hs := weightedIterationSwapDefect_succ_le_generalScale hφ hκ hlower hlam hb U (r + 1 + l) l
      (hscale (r + 1 + l) (by omega) (by omega))
    calc
      _ ≤ M * weightedIterationSwapDefect hφ hκ hlower U (r + 1 + l) l := hs
      _ ≤ M * (M ^ l * weightedIterationSwapDefect hφ hκ hlower U (r + 1) 0) :=
        mul_le_mul_of_nonneg_left hi (by linarith)
      _ = _ := by rw [pow_succ]; ring

/-- BKL (43) with zero-based adjacent-position index l. The Hessian source
is the actual W at level r, and every intervening scale is the literal
normalization ratio of the same recursion. -/
theorem weightedIteration_adjacentSwap_norm_sq_le_generalScale
    (hφsmooth : ContDiff ℝ (⊤ : ℕ∞) φ) {lam M : ℝ} (hlam : 0 < lam) (hM : 1 ≤ M)
    (hb : ∀ g : Lp ℝ 2 (potentialMeasure φ),
      (∑ j, ‖weightedH1Derivative φ j (weightedEnergyInverse hφ hκ hlower g)‖ ^ 2) ≤
        lam⁻¹ * ‖g‖ ^ 2)
    {ι : Type*} [Fintype ι] (U : WeightedH1Family φ ι)
    (F : (k : ℕ) → WeightedIterationIndex n ι k → Space n → ℝ)
    (W : (k : ℕ) → WeightedH1Family φ (Fin n × WeightedIterationIndex n ι k))
    (hF : ∀ k i, ContDiff ℝ 2 (F k i))
    (hW : ∀ k j l i, (weightedH1Derivative φ j (W k (l, i)) : Space n → ℝ)
      =ᵐ[potentialMeasure φ] fun x => coordinateHessian (F k i) x j l)
    (r l : ℕ)
    (hscale : ∀ k, r + 1 ≤ k → k < r + 1 + l →
      (weightedSuccessorScale hφ hκ hlower (weightedSuccessorIterate hφ hκ hlower U k)) ^ 2 ≤ M * lam) :
    weightedIterationSwapDefect hφ hκ hlower U (r + 1 + l) l ≤
      4 * M ^ l * weightedIterationDefect hφsmooth hκ hlower U W r / lam := by
  have hfirst : weightedIterationSwapDefect hφ hκ hlower U (r + 1) 0 ≤
      4 * weightedIterationDefect hφsmooth hκ hlower U W r / lam :=
    weightedNormalizedSuccessor_firstSwap_norm_sq_le hφ hκ hlower hlam
      (weightedSuccessorIterate hφ hκ hlower U r) (W r) (F r) (hF r) (hW r)
      (weightedSuccessorScale_sq_ge_of_inverse_energy hφ hκ hlower hlam hb _)
  calc
    _ ≤ M ^ l * weightedIterationSwapDefect hφ hκ hlower U (r + 1) 0 :=
      weightedIterationSwapDefect_propagation_generalScale hφ hκ hlower hlam hM hb U r l hscale
    _ ≤ M ^ l * (4 * weightedIterationDefect hφsmooth hκ hlower U W r / lam) :=
      mul_le_mul_of_nonneg_left hfirst (pow_nonneg (by linarith) _)
    _ = _ := by ring

end KLS.ConstantReduction
end

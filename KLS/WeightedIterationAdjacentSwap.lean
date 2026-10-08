import KLS.WeightedSuccessorPermutation
import KLS.WeightedIterationBochner

/-! Actual adjacent transpositions on the literal changing-rank tensor
indices. Their squared L² defects propagate along the actual normalized
recursion, starting with the actual Hessian defect. -/

open MeasureTheory InnerProductSpace Matrix
open scoped ContDiff RealInnerProductSpace ENNReal

noncomputable section
namespace KLS

/-- Swap positions l and l+1, counted from zero, of the nested tensor index.
Out-of-range requests are harmless identities. -/
def weightedIterationAdjacentSwap (n : ℕ) (ι : Type*) :
    (k : ℕ) → ℕ → Equiv.Perm (WeightedIterationIndex n ι k)
  | 0, _ => Equiv.refl _
  | 1, _ => Equiv.refl _
  | k + 2, 0 => tensorFirstSwapEquiv (Fin n) (WeightedIterationIndex n ι k)
  | k + 2, l + 1 => Equiv.prodCongr (Equiv.refl (Fin n))
      (weightedIterationAdjacentSwap n ι (k + 1) l)

@[simp] theorem weightedIterationAdjacentSwap_first (n : ℕ) (ι : Type*) (k : ℕ) :
    weightedIterationAdjacentSwap n ι (k + 2) 0 =
      tensorFirstSwapEquiv (Fin n) (WeightedIterationIndex n ι k) := rfl

@[simp] theorem weightedIterationAdjacentSwap_succ (n : ℕ) (ι : Type*) (k l : ℕ) :
    weightedIterationAdjacentSwap n ι (k + 2) (l + 1) =
      Equiv.prodCongr (Equiv.refl (Fin n)) (weightedIterationAdjacentSwap n ι (k + 1) l) := rfl

def weightedGradientAdjacentSwap (n : ℕ) (ι : Type*) (k l : ℕ) :
    Equiv.Perm (Fin n × WeightedIterationIndex n ι k) :=
  weightedIterationAdjacentSwap n ι (k + 1) l

variable {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))

def weightedIterationSwapDefect {ι : Type*} [Fintype ι]
    (U : WeightedH1Family φ ι) (k l : ℕ) : ℝ :=
  ‖weightedFamilyCenteredGradient φ (WeightedIterationIndex n ι k)
      (weightedSuccessorIterate hφ hκ hlower U k) -
    finiteL2Reindex (weightedGradientAdjacentSwap n ι k l)
      (weightedFamilyCenteredGradient φ (WeightedIterationIndex n ι k)
        (weightedSuccessorIterate hφ hκ hlower U k))‖ ^ 2

theorem weightedIterationSwapDefect_nonneg {ι : Type*} [Fintype ι]
    (U : WeightedH1Family φ ι) (k l : ℕ) : 0 ≤ weightedIterationSwapDefect hφ hκ hlower U k l :=
  sq_nonneg _

theorem weightedIterationSwapDefect_succ_le
    {lam : ℝ} (hlam : 0 < lam)
    (hb : ∀ g : Lp ℝ 2 (potentialMeasure φ),
      (∑ j, ‖weightedH1Derivative φ j (weightedEnergyInverse hφ hκ hlower g)‖ ^ 2) ≤
        lam⁻¹ * ‖g‖ ^ 2)
    {ι : Type*} [Fintype ι] (U : WeightedH1Family φ ι) (k l : ℕ)
    (hscale : (weightedSuccessorScale hφ hκ hlower (weightedSuccessorIterate hφ hκ hlower U k)) ^ 2
      ≤ 2 * lam) :
    weightedIterationSwapDefect hφ hκ hlower U (k + 1) (l + 1) ≤
      2 * weightedIterationSwapDefect hφ hκ hlower U k l := by
  exact weightedNormalizedSuccessor_tail_permutation_norm_sq_le hφ hκ hlower hlam hb
    (weightedSuccessorIterate hφ hκ hlower U k) (weightedGradientAdjacentSwap n ι k l) hscale

/-- Propagate an actual first-swap defect through l actual successors. -/
theorem weightedIterationSwapDefect_propagation
    {lam : ℝ} (hlam : 0 < lam)
    (hb : ∀ g : Lp ℝ 2 (potentialMeasure φ),
      (∑ j, ‖weightedH1Derivative φ j (weightedEnergyInverse hφ hκ hlower g)‖ ^ 2) ≤
        lam⁻¹ * ‖g‖ ^ 2)
    {ι : Type*} [Fintype ι] (U : WeightedH1Family φ ι) (r l : ℕ)
    (hscale : ∀ k, r + 1 ≤ k → k < r + 1 + l →
      (weightedSuccessorScale hφ hκ hlower (weightedSuccessorIterate hφ hκ hlower U k)) ^ 2 ≤ 2 * lam) :
    weightedIterationSwapDefect hφ hκ hlower U (r + 1 + l) l ≤
      (2 : ℝ) ^ l * weightedIterationSwapDefect hφ hκ hlower U (r + 1) 0 := by
  induction l with
  | zero => simp
  | succ l ih =>
    have hi := ih (fun k hk hk' => hscale k hk (by omega))
    have hs := weightedIterationSwapDefect_succ_le hφ hκ hlower hlam hb U (r + 1 + l) l
      (hscale (r + 1 + l) (by omega) (by omega))
    calc
      _ ≤ 2 * weightedIterationSwapDefect hφ hκ hlower U (r + 1 + l) l := hs
      _ ≤ 2 * ((2 : ℝ) ^ l * weightedIterationSwapDefect hφ hκ hlower U (r + 1) 0) :=
        mul_le_mul_of_nonneg_left hi (by norm_num)
      _ = _ := by rw [pow_succ]; ring

/-- BKL (43) with zero-based adjacent-position index l. The Hessian source
is the actual W at level r, and every intervening scale is the literal
normalization ratio of the same recursion. -/
theorem weightedIteration_adjacentSwap_norm_sq_le
    (hφsmooth : ContDiff ℝ (⊤ : ℕ∞) φ) {lam : ℝ} (hlam : 0 < lam)
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
      (weightedSuccessorScale hφ hκ hlower (weightedSuccessorIterate hφ hκ hlower U k)) ^ 2 ≤ 2 * lam) :
    weightedIterationSwapDefect hφ hκ hlower U (r + 1 + l) l ≤
      (2 : ℝ) ^ (l + 2) * weightedIterationDefect hφsmooth hκ hlower U W r / lam := by
  have hfirst : weightedIterationSwapDefect hφ hκ hlower U (r + 1) 0 ≤
      4 * weightedIterationDefect hφsmooth hκ hlower U W r / lam :=
    weightedNormalizedSuccessor_firstSwap_norm_sq_le hφ hκ hlower hlam
      (weightedSuccessorIterate hφ hκ hlower U r) (W r) (F r) (hF r) (hW r)
      (weightedSuccessorScale_sq_ge_of_inverse_energy hφ hκ hlower hlam hb _)
  calc
    _ ≤ (2 : ℝ) ^ l * weightedIterationSwapDefect hφ hκ hlower U (r + 1) 0 :=
      weightedIterationSwapDefect_propagation hφ hκ hlower hlam hb U r l hscale
    _ ≤ (2 : ℝ) ^ l * (4 * weightedIterationDefect hφsmooth hκ hlower U W r / lam) :=
      mul_le_mul_of_nonneg_left hfirst (pow_nonneg (by norm_num) _)
    _ = _ := by rw [pow_add]; norm_num; ring

end KLS
end

#print axioms KLS.weightedIterationSwapDefect_propagation
#print axioms KLS.weightedIteration_adjacentSwap_norm_sq_le

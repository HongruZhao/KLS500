import KLS.WeightedTensorAdjacentAction
import KLS.FiniteGroupSymmetrization
import KLS.RouteArithmetic

/-! BKL Lemma 3.3 for the actual normalized iteration. The symmetrizer is the
literal average of all permutations of the first q+1 tensor positions.
The bound uses the actual squared Hessian defects and actual scale ratios. -/

open MeasureTheory InnerProductSpace Matrix
open scoped ContDiff RealInnerProductSpace ENNReal BigOperators

noncomputable section
namespace KLS
variable {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))

/-- Average the first q+1 positions of the actual centered gradient at level
r+q, leaving its r-position suffix and original family index fixed. -/
def weightedIterationSymmetrizedGradient {ι : Type*} [Fintype ι]
    (U : WeightedH1Family φ ι) (r q : ℕ) :
    CenteredL2.Family (potentialMeasure φ) (Fin n × WeightedIterationIndex n ι (r + q)) :=
  finiteIsometryAverage (weightedGradientPermutationAction (potentialMeasure φ) n ι r q)
    (weightedFamilyCenteredGradient φ (WeightedIterationIndex n ι (r + q))
      (weightedSuccessorIterate hφ hκ hlower U (r + q)))

theorem weightedIterationSymmetrizedGradient_fixed {ι : Type*} [Fintype ι]
    (U : WeightedH1Family φ ι) (r q : ℕ) (σ : Equiv.Perm (Fin (q + 1))) :
    finiteL2Reindex (weightedGradientPrefixPermutationHom n ι r q σ)
      (weightedIterationSymmetrizedGradient hφ hκ hlower U r q) =
        weightedIterationSymmetrizedGradient hφ hκ hlower U r q :=
  finiteIsometryAverage_fixed (weightedGradientPermutationAction (potentialMeasure φ) n ι r q)
    (weightedFamilyCenteredGradient φ (WeightedIterationIndex n ι (r + q))
      (weightedSuccessorIterate hφ hκ hlower U (r + q))) σ

theorem weightedIteration_symmetrization_le_adjacent_defects {ι : Type*} [Fintype ι]
    (U : WeightedH1Family φ ι) (r q : ℕ) :
    ‖weightedFamilyCenteredGradient φ (WeightedIterationIndex n ι (r + q))
        (weightedSuccessorIterate hφ hκ hlower U (r + q)) -
      weightedIterationSymmetrizedGradient hφ hκ hlower U r q‖ ^ 2 ≤
        4 * (q + 1 : ℝ) ^ 4 * ∑ i : Fin q, weightedIterationSwapDefect hφ hκ hlower U (r + q) i := by
  have h := norm_sub_permutationAverage_sq_le
    (weightedGradientPermutationAction (potentialMeasure φ) n ι r q)
    (weightedFamilyCenteredGradient φ (WeightedIterationIndex n ι (r + q))
      (weightedSuccessorIterate hφ hκ hlower U (r + q)))
  simpa only [weightedIterationSymmetrizedGradient, weightedIterationSwapDefect,
    weightedGradientPermutationAction_adjacent] using h

theorem symmetrization_coefficient_le_128 (q : ℕ) :
    4 * (q + 1 : ℝ) ^ 4 * (2 : ℝ) ^ (q + 1) ≤ (128 : ℝ) ^ (q + 1) := by
  have hbase : (q + 1 : ℝ) ^ 4 * (2 : ℝ) ^ (q + 1) ≤ (32 : ℝ) ^ (q + 1) := by
    exact_mod_cast RouteArithmetic.symmetrization_coefficient_le (q + 1)
  have hfour : (4 : ℝ) ≤ (4 : ℝ) ^ (q + 1) := by
    have h : (1 : ℝ) ≤ 4 ^ q := one_le_pow₀ (show (1 : ℝ) ≤ 4 by norm_num)
    rw [pow_succ]
    nlinarith
  calc
    _ = 4 * ((q + 1 : ℝ) ^ 4 * (2 : ℝ) ^ (q + 1)) := by ring
    _ ≤ 4 * (32 : ℝ) ^ (q + 1) := mul_le_mul_of_nonneg_left hbase (by norm_num)
    _ ≤ (4 : ℝ) ^ (q + 1) * (32 : ℝ) ^ (q + 1) :=
      mul_le_mul_of_nonneg_right hfour (by positivity)
    _ = _ := by rw [← mul_pow]; norm_num

/-- The sum of the actual adjacent defects is controlled by precisely the
preceding q actual Hessian defects; each relevant scale is the actual ratio. -/
theorem weightedIteration_sum_adjacent_defects_le
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
    (r q : ℕ)
    (hscale : ∀ k, r + 1 ≤ k → k < r + q →
      (weightedSuccessorScale hφ hκ hlower (weightedSuccessorIterate hφ hκ hlower U k)) ^ 2 ≤ 2 * lam) :
    (∑ i : Fin q, weightedIterationSwapDefect hφ hκ hlower U (r + q) i) ≤
      (2 : ℝ) ^ (q + 1) / lam * ∑ i : Fin q, weightedIterationDefect hφsmooth hκ hlower U W (r + i) := by
  have hi (i : Fin q) : weightedIterationSwapDefect hφ hκ hlower U (r + q) i ≤
      ((2 : ℝ) ^ (q + 1) / lam) *
        weightedIterationDefect hφsmooth hκ hlower U W (r + i.rev) := by
    have he : r + (i.rev : ℕ) + 1 + (i : ℕ) = r + q := by
      rw [Fin.val_rev]
      omega
    have h := weightedIteration_adjacentSwap_norm_sq_le hφ hκ hlower hφsmooth hlam hb
      U F W hF hW (r + i.rev) i (fun k hk hk' => hscale k (by omega) (by omega))
    rw [he] at h
    have hp : (2 : ℝ) ^ ((i : ℕ) + 2) ≤ (2 : ℝ) ^ (q + 1) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hd := weightedIterationDefect_nonneg hφsmooth hκ hlower U W (r + i.rev)
    calc
      _ ≤ (2 : ℝ) ^ ((i : ℕ) + 2) *
          weightedIterationDefect hφsmooth hκ hlower U W (r + i.rev) / lam := h
      _ ≤ (2 : ℝ) ^ (q + 1) *
          weightedIterationDefect hφsmooth hκ hlower U W (r + i.rev) / lam :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hp hd) hlam.le
      _ = _ := by ring
  have hrev : (∑ i : Fin q, weightedIterationDefect hφsmooth hκ hlower U W (r + i.rev)) =
      ∑ i : Fin q, weightedIterationDefect hφsmooth hκ hlower U W (r + i) :=
    Equiv.sum_comp Fin.revPerm (fun i : Fin q => weightedIterationDefect hφsmooth hκ hlower U W (r + i))
  calc
    _ ≤ ∑ i : Fin q, ((2 : ℝ) ^ (q + 1) / lam) *
        weightedIterationDefect hφsmooth hκ hlower U W (r + i.rev) :=
      Finset.sum_le_sum (fun i _ => hi i)
    _ = _ := by rw [← Finset.mul_sum, hrev]

/-- BKL Lemma 3.3 with the explicit universal constant 128. All tensors,
permutations, normalization ratios, and defects are the actual constructed
ones. The hypotheses on F/W are supplied by the smooth-iteration theorem. -/
theorem weightedIteration_symmetrization_bound
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
    (r q : ℕ)
    (hscale : ∀ k, r + 1 ≤ k → k < r + q →
      (weightedSuccessorScale hφ hκ hlower (weightedSuccessorIterate hφ hκ hlower U k)) ^ 2 ≤ 2 * lam) :
    ‖weightedFamilyCenteredGradient φ (WeightedIterationIndex n ι (r + q))
        (weightedSuccessorIterate hφ hκ hlower U (r + q)) -
      weightedIterationSymmetrizedGradient hφ hκ hlower U r q‖ ^ 2 ≤
        (128 : ℝ) ^ (q + 1) / lam *
          ∑ i : Fin q, weightedIterationDefect hφsmooth hκ hlower U W (r + i) := by
  have hsum := weightedIteration_sum_adjacent_defects_le hφ hκ hlower hφsmooth hlam hb U F W hF hW r q hscale
  have hS : 0 ≤ ∑ i : Fin q, weightedIterationDefect hφsmooth hκ hlower U W (r + i) :=
    Finset.sum_nonneg (fun i _ => weightedIterationDefect_nonneg hφsmooth hκ hlower U W (r + i))
  calc
    _ ≤ 4 * (q + 1 : ℝ) ^ 4 *
        ∑ i : Fin q, weightedIterationSwapDefect hφ hκ hlower U (r + q) i :=
      weightedIteration_symmetrization_le_adjacent_defects hφ hκ hlower U r q
    _ ≤ 4 * (q + 1 : ℝ) ^ 4 * ((2 : ℝ) ^ (q + 1) / lam *
        ∑ i : Fin q, weightedIterationDefect hφsmooth hκ hlower U W (r + i)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (4 * (q + 1 : ℝ) ^ 4 * (2 : ℝ) ^ (q + 1)) / lam *
        ∑ i : Fin q, weightedIterationDefect hφsmooth hκ hlower U W (r + i) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (symmetrization_coefficient_le_128 q) hlam.le) hS

end KLS
end

#print axioms KLS.weightedIterationSymmetrizedGradient_fixed
#print axioms KLS.weightedIteration_symmetrization_bound

import WeightedScaleSymmetrization
import SpectralReductionPermutationIndividualBound
import TwoPointWeightedSymmetrization

open MeasureTheory Matrix
open scoped ContDiff BigOperators
noncomputable section
namespace KLS.ConstantReduction

def individualSymmetrizationCoefficient (q : ℕ) : ℝ :=
  if q = 1 then 1 else (q : ℝ) * (q + 1 : ℝ)

theorem individualSymmetrizationCoefficient_nonneg (q : ℕ) :
    0 ≤ individualSymmetrizationCoefficient q := by
  unfold individualSymmetrizationCoefficient
  split_ifs <;> positivity

variable {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]

theorem weightedIteration_symmetrization_bound_individual_weightedScale
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
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
    (r q : ℕ)
    (hscale : ∀ k, r+1 ≤ k → k < r+q →
      (weightedSuccessorScale hφ hκ hlower (weightedSuccessorIterate hφ hκ hlower U k))^2 ≤
        M*lam) :
    ‖weightedFamilyCenteredGradient φ (WeightedIterationIndex n ι (r+q))
        (weightedSuccessorIterate hφ hκ hlower U (r+q)) -
      weightedIterationSymmetrizedGradient hφ hκ hlower U r q‖^2 ≤
      ((q : ℝ)*(q+1 : ℝ))/lam *
        ∑ i : Fin q, ((i : ℕ)+1 : ℝ)*M^(i.rev : ℕ)*weightedIterationDefect hφsmooth hκ hlower U W (r+i) := by
  have hav := norm_sub_permutationAverage_sq_le_individual
    (weightedGradientPermutationAction (potentialMeasure φ) n ι r q)
    (weightedFamilyCenteredGradient φ (WeightedIterationIndex n ι (r+q))
      (weightedSuccessorIterate hφ hκ hlower U (r+q)))
  have hi (i : Fin q) : weightedIterationSwapDefect hφ hκ hlower U (r+q) i ≤
      (4/lam)*(M^(i : ℕ)*weightedIterationDefect hφsmooth hκ hlower U W (r+i.rev)) := by
    have he : r+(i.rev : ℕ)+1+(i : ℕ)=r+q := by rw [Fin.val_rev]; omega
    have hh := weightedIteration_adjacentSwap_norm_sq_le_generalScale hφ hκ hlower hφsmooth hlam hM hb
      U F W hF hW (r+i.rev) i (fun k hk hk' => hscale k (by omega) (by omega))
    rw [he] at hh
    convert hh using 1
    ring
  have hrev : (∑ i : Fin q, ((q-(i : ℕ) : ℕ) : ℝ)*M^(i : ℕ)*
      weightedIterationDefect hφsmooth hκ hlower U W (r+i.rev)) =
      ∑ i : Fin q, ((i : ℕ)+1 : ℝ)*M^(i.rev : ℕ)*
        weightedIterationDefect hφsmooth hκ hlower U W (r+i) := by
    have hc (i : Fin q) : (q-(i : ℕ) : ℕ)=(i.rev : ℕ)+1 := by rw [Fin.val_rev]; omega
    simp_rw [hc, Nat.cast_add, Nat.cast_one]
    simpa only [Fin.revPerm_apply, Fin.rev_rev] using Equiv.sum_comp Fin.revPerm
      (fun i : Fin q => ((i : ℕ)+1 : ℝ)*M^(i.rev : ℕ)*
        weightedIterationDefect hφsmooth hκ hlower U W (r+i))
  have hsum : (∑ i : Fin q, ((q-(i : ℕ) : ℕ) : ℝ)*
      weightedIterationSwapDefect hφ hκ hlower U (r+q) i) ≤
      (4/lam)*∑ i : Fin q, ((i : ℕ)+1 : ℝ)*M^(i.rev : ℕ)*
        weightedIterationDefect hφsmooth hκ hlower U W (r+i) := by
    calc
      _ ≤ ∑ i : Fin q, ((q-(i : ℕ) : ℕ) : ℝ)*
          ((4/lam)*(M^(i : ℕ)*weightedIterationDefect hφsmooth hκ hlower U W (r+i.rev))) := by
        exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hi i) (Nat.cast_nonneg _)
      _ = (4/lam)*∑ i : Fin q, ((q-(i : ℕ) : ℕ) : ℝ)*M^(i : ℕ)*
          weightedIterationDefect hφsmooth hκ hlower U W (r+i.rev) := by rw [Finset.mul_sum]; congr 1; funext i; ring
      _ = _ := by rw [hrev]
  calc
    _ ≤ ((q : ℝ)*(q+1 : ℝ)/4)*
        ∑ i : Fin q, ((q-(i : ℕ) : ℕ) : ℝ)*weightedIterationSwapDefect hφ hκ hlower U (r+q) i := by
      simpa only [weightedIterationSymmetrizedGradient, weightedIterationSwapDefect,
        weightedGradientPermutationAction_adjacent] using hav
    _ ≤ ((q : ℝ)*(q+1 : ℝ)/4)*((4/lam) *
        ∑ i : Fin q, ((i : ℕ)+1 : ℝ)*M^(i.rev : ℕ)*weightedIterationDefect hφsmooth hκ hlower U W (r+i)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

theorem weightedIteration_symmetrization_bound_rankIndividualScale
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
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
    (r q : ℕ)
    (hscale : ∀ k, r+1 ≤ k → k < r+q →
      (weightedSuccessorScale hφ hκ hlower (weightedSuccessorIterate hφ hκ hlower U k))^2 ≤
        M*lam) :
    ‖weightedFamilyCenteredGradient φ (WeightedIterationIndex n ι (r+q))
        (weightedSuccessorIterate hφ hκ hlower U (r+q)) -
      weightedIterationSymmetrizedGradient hφ hκ hlower U r q‖^2 ≤
      individualSymmetrizationCoefficient q / lam *
        ∑ i : Fin q, ((i : ℕ)+1 : ℝ)*M^(i.rev : ℕ)*weightedIterationDefect hφsmooth hκ hlower U W (r+i) := by
  by_cases hq : q = 1
  · subst q
    simpa [individualSymmetrizationCoefficient] using
      weightedIteration_symmetrization_bound_finTwo hφ hκ hlower hφsmooth hlam hb U F W hF hW r
  · simpa only [individualSymmetrizationCoefficient, ite_eq_right hq] using
      weightedIteration_symmetrization_bound_individual_weightedScale hφ hκ hlower
        hφsmooth hlam hM hb U F W hF hW r q hscale

end KLS.ConstantReduction
end

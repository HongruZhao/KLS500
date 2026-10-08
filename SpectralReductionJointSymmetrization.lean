import WeightedScaleSymmetrization
import OptJointPermutationAverageBound
import SpectralReductionIndividualSymmetrization
import TwoPointWeightedSymmetrization

open MeasureTheory Matrix
open scoped ContDiff BigOperators
noncomputable section
namespace KLS.ConstantReduction

def jointSymmetrizationWeight (q : ℕ) (i : Fin q) : ℝ :=
  4*meanInsertionDefectWeight q (i.rev : ℕ)

theorem jointSymmetrizationWeight_nonneg (q : ℕ) (i : Fin q) :
    0≤jointSymmetrizationWeight q i :=
  mul_nonneg (by norm_num) (meanInsertionDefectWeight_nonneg _ _)

variable {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]

theorem weightedIteration_symmetrization_bound_rankJointScale
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
      (4/lam) *
        ∑ i : Fin q, meanInsertionDefectWeight q (i.rev : ℕ)*M^(i.rev : ℕ)*weightedIterationDefect hφsmooth hκ hlower U W (r+i) := by
  have hav := norm_sub_permutationAverage_sq_le_joint_individual
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
  have hrev : (∑ i : Fin q, meanInsertionDefectWeight q (i : ℕ)*M^(i : ℕ)*
      weightedIterationDefect hφsmooth hκ hlower U W (r+i.rev)) =
      ∑ i : Fin q, meanInsertionDefectWeight q (i.rev : ℕ)*M^(i.rev : ℕ)*
        weightedIterationDefect hφsmooth hκ hlower U W (r+i) := by
    simpa only [Fin.revPerm_apply, Fin.rev_rev] using Equiv.sum_comp Fin.revPerm
      (fun i : Fin q => meanInsertionDefectWeight q (i.rev : ℕ)*M^(i.rev : ℕ)*
        weightedIterationDefect hφsmooth hκ hlower U W (r+i))
  have hsum : (∑ i : Fin q, meanInsertionDefectWeight q (i : ℕ)*
      weightedIterationSwapDefect hφ hκ hlower U (r+q) i) ≤
      (4/lam)*∑ i : Fin q, meanInsertionDefectWeight q (i.rev : ℕ)*M^(i.rev : ℕ)*
        weightedIterationDefect hφsmooth hκ hlower U W (r+i) := by
    calc
      _ ≤ ∑ i : Fin q, meanInsertionDefectWeight q (i : ℕ)*
          ((4/lam)*(M^(i : ℕ)*weightedIterationDefect hφsmooth hκ hlower U W (r+i.rev))) := by
        exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hi i) (meanInsertionDefectWeight_nonneg _ _)
      _ = (4/lam)*∑ i : Fin q, meanInsertionDefectWeight q (i : ℕ)*M^(i : ℕ)*
          weightedIterationDefect hφsmooth hκ hlower U W (r+i.rev) := by rw [Finset.mul_sum]; congr 1; funext i; ring
      _ = _ := by rw [hrev]
  calc
    _ ≤ ∑ i : Fin q, meanInsertionDefectWeight q (i : ℕ)*weightedIterationSwapDefect hφ hκ hlower U (r+q) i := by
      simpa only [weightedIterationSymmetrizedGradient, weightedIterationSwapDefect,
        weightedGradientPermutationAction_adjacent] using hav
    _ ≤ _ := hsum

end KLS.ConstantReduction
end

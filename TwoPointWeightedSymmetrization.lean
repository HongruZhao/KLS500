import FiniteAverageTwoPoint
import KLS.WeightedIterationSymmetrization

open MeasureTheory InnerProductSpace Matrix
open scoped ContDiff RealInnerProductSpace ENNReal BigOperators
noncomputable section
namespace KLS.ConstantReduction
variable {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]

/-- The d=1 symmetrizer has exactly one quarter of the adjacent defect,
so its actual Hessian-error coefficient is 1/lambda. No scale premise is
needed for this single adjacent swap. -/
theorem weightedIteration_symmetrization_bound_finTwo
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
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
    (r : ℕ) :
    ‖weightedFamilyCenteredGradient φ (WeightedIterationIndex n ι (r + 1))
        (weightedSuccessorIterate hφ hκ hlower U (r + 1)) -
      weightedIterationSymmetrizedGradient hφ hκ hlower U r 1‖ ^ 2 ≤
      1 / lam * weightedIterationDefect hφsmooth hκ hlower U W r := by
  have he := norm_sub_finiteIsometryAverage_finTwo_sq
    (weightedGradientPermutationAction (potentialMeasure φ) n ι r 1)
    (weightedFamilyCenteredGradient φ (WeightedIterationIndex n ι (r + 1))
      (weightedSuccessorIterate hφ hκ hlower U (r + 1)))
  have heq :
      ‖weightedFamilyCenteredGradient φ (WeightedIterationIndex n ι (r + 1))
          (weightedSuccessorIterate hφ hκ hlower U (r + 1)) -
        weightedIterationSymmetrizedGradient hφ hκ hlower U r 1‖ ^ 2 =
        (1/4 : ℝ) * weightedIterationSwapDefect hφ hκ hlower U (r + 1) 0 := by
    simpa only [weightedIterationSymmetrizedGradient, weightedIterationSwapDefect,
      weightedGradientPermutationAction_adjacent, Fin.val_zero] using he
  have hb' := weightedIteration_sum_adjacent_defects_le hφ hκ hlower hφsmooth hlam hb
    U F W hF hW r 1 (fun k hk hk' => by omega)
  simp only [Fin.sum_univ_one, Fin.val_zero, Nat.add_zero] at hb'
  norm_num at hb'
  rw [heq]
  calc
    _ ≤ (1/4 : ℝ) * (4 / lam *
        weightedIterationDefect hφsmooth hκ hlower U W r) :=
      mul_le_mul_of_nonneg_left hb' (by norm_num)
    _ = _ := by norm_num; ring

end KLS.ConstantReduction
end

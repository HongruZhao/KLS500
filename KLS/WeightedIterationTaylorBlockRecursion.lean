import KLS.WeightedIterationTaylorBlock

/-! The genuine one-step Taylor recursion on a fixed ambient tensor carrier.
The subgroup average moves precisely the Taylor and next derivative indices. -/

open MeasureTheory Matrix
open scoped ContDiff RealInnerProductSpace Topology BigOperators
noncomputable section
namespace KLS
variable {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
  {ι : Type*} [Fintype ι] (U : WeightedH1Family φ ι)
  (F : (k : ℕ) → WeightedIterationIndex n ι k → Space n → ℝ)
  (hF : ∀ k i, ContDiff ℝ (⊤ : ℕ∞) (F k i))
  (hV : ∀ k i, F k i =ᵐ[volume] (weightedH1Value φ
    (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U k i) : Space n → ℝ))
  (hL : ∀ k i, MemLp (weightedDiffusion φ (F k i)) 2 (potentialMeasure φ))

include hF hV hL

theorem weightedIterationBlockTaylor_step (r d q m : ℕ) (h : d + (q + 1) = m)
    (hd : d ≠ 0) :
    finiteIsometryAverage
      (realTensorPrefixAction n (m + 1) (WeightedIterationIndex n ι r) (by omega : d + 1 ≤ m + 1))
      (weightedIterationBlockTaylor (hφ.of_le (by simp)) hκ hlower U r d (q + 1) m h) =
      weightedSuccessorScale (hφ.of_le (by simp)) hκ hlower
        (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U (r + q)) •
          weightedIterationBlockTaylor (hφ.of_le (by simp)) hκ hlower U r (d + 1) q m (by omega) := by
  apply PiLp.ext
  rintro ⟨a, i⟩
  let b := finBlockTuple a 0 (d + 1) (by omega)
  let ji : WeightedIterationIndex n ι (r + q + 1) :=
    (tensorPrefixEquiv n ι r (q + 1)).symm (finBlockTuple a (d + 1) (q + 1) (by omega), i)
  have he := congrArg (fun T : EuclideanSpace ℝ
      ((Fin (d + 1) → Fin n) × WeightedIterationIndex n ι (r + q + 1)) => T (b, ji))
    (weightedIteration_taylor_action_recursion hφ hκ hlower U F hF hV hL (r + q) hd)
  calc
    _ = finiteIsometryAverage
        (realCoordinatePermutationAction n (d + 1) (WeightedIterationIndex n ι (r + q + 1)))
        (weightedL2GradientTaylor φ d
          (weightedFamilyCenteredGradient φ (WeightedIterationIndex n ι (r + q + 1))
            (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U (r + q + 1)))) (b, ji) := by
      rw [realTensorPrefixAverage_apply, realCoordinatePermutationAverage_apply]
      congr 1
      apply Finset.sum_congr rfl
      intro σ _
      rw [weightedIterationBlockTaylor_step_entry,
        finBlockTuple_prefix_permutation a (le_refl (d + 1)),
        finBlockTuple_suffix_permutation a _ _ (le_refl (d + 1))]
      rfl
    _ = _ := he

end KLS
end

#print axioms KLS.weightedIterationBlockTaylor_step

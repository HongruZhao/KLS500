import KLS.WeightedIterationTaylorRepeat
import KLS.TaylorBlockIsometry

/-! BKL (56) with a fixed affected prefix and a retained suffix of derivative
indices. This form can be placed on exactly the first 3d tensor positions. -/

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
  (hF : ∀ k i, ContDiff ℝ (⊤ : ℕ∞) (F k i))
  (hV : ∀ k i, F k i =ᵐ[volume] (weightedH1Value φ
    (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U k i) : Space n → ℝ))
  (hL : ∀ k i, MemLp (weightedDiffusion φ (F k i)) 2 (potentialMeasure φ))

include hF hV hL

/-- Exactly k Taylor-recursion steps; q+1 original derivative positions are
retained, and every coordinate after t=d+k is fixed by the average. -/
theorem weightedIterationBlockTaylor_partial (r d q k t m : ℕ)
    (hdk : d + k = t) (h : t + q = m) (hd : d ≠ 0) :
    finiteIsometryAverage
      (realTensorPrefixAction n (m + 1) (WeightedIterationIndex n ι r) (by omega : t ≤ m + 1))
      (weightedIterationBlockTaylor (hφ.of_le (by simp)) hκ hlower U r d (q + k) m (by omega)) =
      (∏ j ∈ Finset.range k, weightedSuccessorScale (hφ.of_le (by simp)) hκ hlower
        (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U (r + q + j))) •
          weightedIterationBlockTaylor (hφ.of_le (by simp)) hκ hlower U r t q m h := by
  induction k generalizing d with
  | zero =>
    have he : d = t := by omega
    subst d
    simp only [Nat.add_zero, Finset.range_zero, Finset.prod_empty, one_smul]
    exact finiteIsometryAverage_eq_of_forall_fixed _ _
      (weightedIterationBlockTaylor_taylor_fixed hφ hκ hlower U r t q m h)
  | succ k ih =>
    let S := finiteIsometryAverageLinearMap
      (realTensorPrefixAction n (m + 1) (WeightedIterationIndex n ι r) (by omega : t ≤ m + 1))
    let α := weightedSuccessorScale (hφ.of_le (by simp)) hκ hlower
      (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U (r + (q + k)))
    change S _ = _
    calc
      _ = S (finiteIsometryAverage
          (realTensorPrefixAction n (m + 1) (WeightedIterationIndex n ι r) (by omega : d + 1 ≤ m + 1))
          (weightedIterationBlockTaylor (hφ.of_le (by simp)) hκ hlower U r d (q + k + 1) m (by omega))) := by
        exact (realTensorPrefixAverage_absorb n (m + 1) (WeightedIterationIndex n ι r)
          (by omega : d + 1 ≤ t) (by omega : t ≤ m + 1) _).symm
      _ = S (α • weightedIterationBlockTaylor (hφ.of_le (by simp)) hκ hlower U r (d + 1) (q + k) m (by omega)) := by
        rw [weightedIterationBlockTaylor_step hφ hκ hlower U F hF hV hL r d (q + k) m (by omega) hd]
      _ = α • S (weightedIterationBlockTaylor (hφ.of_le (by simp)) hκ hlower U r (d + 1) (q + k) m (by omega)) :=
        S.map_smul _ _
      _ = α • ((∏ j ∈ Finset.range k, weightedSuccessorScale (hφ.of_le (by simp)) hκ hlower
          (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U (r + q + j))) •
            weightedIterationBlockTaylor (hφ.of_le (by simp)) hκ hlower U r t q m h) := by
        rw [show S (weightedIterationBlockTaylor (hφ.of_le (by simp)) hκ hlower U r (d + 1) (q + k) m (by omega)) = _
          from ih (d + 1) (by omega) (by omega)]
      _ = _ := by
        rw [smul_smul, Finset.prod_range_succ, mul_comm]
        simp only [α]
        have hs := congrArg (fun ℓ => weightedSuccessorScale (hφ.of_le (by simp)) hκ hlower
          (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U ℓ)) (Nat.add_assoc r q k)
        rw [← hs]

end KLS
end

#print axioms KLS.weightedIterationBlockTaylor_partial

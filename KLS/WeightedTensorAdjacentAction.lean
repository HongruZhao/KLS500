import KLS.WeightedTensorPermutationAction

/-! The adjacent generators of the genuine prefix-permutation action are
exactly the adjacent swaps already used in the actual iterative estimates. -/

open MeasureTheory
noncomputable section
namespace KLS

set_option backward.isDefEq.respectTransparency false

@[simp] theorem adjacentFinSwap_symm {q : ℕ} (i : Fin q) :
    (adjacentFinSwap q i).symm = adjacentFinSwap q i := rfl

@[simp] theorem adjacentFinSwap_succ_zero {q : ℕ} (i : Fin q) :
    adjacentFinSwap (q + 1) i.succ 0 = 0 := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro h
    have hv := congrArg Fin.val h
    simp at hv
  · exact (Fin.succ_ne_zero _).symm

@[simp] theorem adjacentFinSwap_succ_succ {q : ℕ} (i : Fin q) (j : Fin (q + 1)) :
    adjacentFinSwap (q + 1) i.succ j.succ = (adjacentFinSwap q i j).succ := by
  exact (Function.Injective.map_swap (Fin.succ_injective (q + 1)) i.castSucc i.succ j).symm

theorem tensorPrefixEquiv_adjacentSwap (n : ℕ) (ι : Type*) (r q : ℕ)
    (i : Fin q) (x : WeightedIterationIndex n ι (r + (q + 1))) :
    tensorPrefixEquiv n ι r (q + 1)
      (weightedIterationAdjacentSwap n ι (r + (q + 1)) i x) =
      (fun j => (tensorPrefixEquiv n ι r (q + 1) x).1 (adjacentFinSwap q i j),
        (tensorPrefixEquiv n ι r (q + 1) x).2) := by
  induction q with
  | zero => exact Fin.elim0 i
  | succ q ih =>
    induction i using Fin.cases with
    | zero =>
      rcases x with ⟨a, b, y⟩
      change ((Fin.cons b (Fin.cons a (tensorPrefixEquiv n ι r q y).1) : Fin (q + 2) → Fin n),
          (tensorPrefixEquiv n ι r q y).2) = _
      apply Prod.ext
      · funext j
        induction j using Fin.cases with
        | zero =>
          simp [adjacentFinSwap, tensorPrefixEquiv]
          rfl
        | succ j =>
          induction j using Fin.cases with
          | zero =>
            simp [adjacentFinSwap, tensorPrefixEquiv]
            rfl
          | succ j =>
            have h0 : j.succ.succ ≠ (0 : Fin (q + 2)) := Fin.succ_ne_zero _
            have h1 : j.succ.succ ≠ (1 : Fin (q + 2)) := by
              intro h
              have hv := congrArg Fin.val h
              simp at hv
            simp [adjacentFinSwap, tensorPrefixEquiv, Equiv.swap_apply_of_ne_of_ne h0 h1]
            rfl
      · rfl
    | succ i =>
      rcases x with ⟨a, y⟩
      change ((Fin.cons a (tensorPrefixEquiv n ι r (q + 1)
          (weightedIterationAdjacentSwap n ι (r + (q + 1)) i y)).1 : Fin (q + 2) → Fin n),
          (tensorPrefixEquiv n ι r (q + 1)
            (weightedIterationAdjacentSwap n ι (r + (q + 1)) i y)).2) = _
      rw [ih i y]
      apply Prod.ext
      · funext j
        induction j using Fin.cases with
        | zero =>
          simp [tensorPrefixEquiv]
          rfl
        | succ j =>
          simp [tensorPrefixEquiv]
          rfl
      · rfl

theorem weightedGradientPrefixPermutationHom_adjacent (n : ℕ) (ι : Type*) (r q : ℕ)
    (i : Fin q) :
    weightedGradientPrefixPermutationHom n ι r q (adjacentFinSwap q i) =
      weightedGradientAdjacentSwap n ι (r + q) i := by
  apply Equiv.ext
  intro x
  apply (tensorPrefixEquiv n ι r (q + 1)).injective
  change tensorPrefixEquiv n ι r (q + 1)
    (tensorPrefixPermutationHom n ι r (q + 1) (adjacentFinSwap q i) x) = _
  have he := tensorPrefixPermutationHom_apply n ι r (q + 1) (adjacentFinSwap q i)
    (show WeightedIterationIndex n ι (r + (q + 1)) from x)
  rw [he, Equiv.apply_symm_apply, adjacentFinSwap_symm]
  exact (tensorPrefixEquiv_adjacentSwap n ι r q i x).symm

theorem weightedGradientPermutationAction_adjacent
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (n : ℕ) (ι : Type*) [Fintype ι]
    (r q : ℕ) (i : Fin q) :
    weightedGradientPermutationAction μ n ι r q (adjacentFinSwap q i) =
      finiteL2Reindex (weightedGradientAdjacentSwap n ι (r + q) i) := by
  change finiteL2Reindex (weightedGradientPrefixPermutationHom n ι r q (adjacentFinSwap q i)) = _
  rw [weightedGradientPrefixPermutationHom_adjacent]

end KLS
end

#print axioms KLS.tensorPrefixEquiv_adjacentSwap
#print axioms KLS.weightedGradientPermutationAction_adjacent

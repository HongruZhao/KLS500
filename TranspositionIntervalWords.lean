import PermutationSquareWord

/-! Actual adjacent words for a transposition retain their interval support,
distance-dependent length, and individual generator counts. -/

namespace KLS.ConstantReduction

theorem exists_adjacentFinSwapWord_interval {q : ℕ}
    (i j : Fin (q+1)) (hij : i < j) :
    ∃ w : List (Fin q), (w.map (adjacentFinSwap q)).prod = Equiv.swap i j ∧
      w.length ≤ 2*((j : ℕ)-(i : ℕ))-1 ∧
      (∀ k ∈ w, (i : ℕ) ≤ k ∧ (k : ℕ) < j) ∧
      ∀ k, w.count k ≤ 2 := by
  induction j using Fin.induction with
  | zero => exact False.elim (Fin.not_lt_zero i hij)
  | succ j ih =>
    obtain rfl | hlt := (Fin.le_castSucc_iff.mpr hij).eq_or_lt
    · refine ⟨[j], ?_, ?_, ?_, ?_⟩
      · simp [adjacentFinSwap]
      · simp
      · intro k hk
        have hk' : k=j := by simpa using hk
        subst k
        simp
      · intro k
        have hh : ([j] : List (Fin q)).count k ≤ 1 := by
          exact List.nodup_iff_count_le_one.mp (by simp) k
        omega
    · obtain ⟨w, hw, hlen, hsupp, hcount⟩ := ih hlt
      have hjnot : j ∉ w := by
        intro hj
        have hh := (hsupp j hj).2
        simp only [Fin.val_castSucc] at hh
        omega
      refine ⟨j :: (w ++ [j]), ?_, ?_, ?_, ?_⟩
      · rw [List.map_cons, List.map_append, List.prod_cons, List.prod_append,
          List.map_singleton, List.prod_singleton, hw, ← mul_assoc]
        exact (Equiv.swap_mul_swap_mul_swap hlt.ne hij.ne).trans (Equiv.swap_comm _ _)
      · simp only [List.length_cons, List.length_append, List.length_nil,
          Fin.val_succ, Fin.val_castSucc] at hlen ⊢
        have hi : (i : ℕ)<j := hlt
        omega
      · intro k hk
        have hk' : k=j ∨ k∈w ∨ k=j := by simpa using hk
        clear hk
        rcases hk' with hk | hk | hk
        · subst k
          have hi : (i : ℕ)<j := hlt
          simp only [Fin.val_succ]
          omega
        · have hh := hsupp k hk
          simp only [Fin.val_castSucc] at hh
          simp only [Fin.val_succ]
          omega
        · subst k
          have hi : (i : ℕ)<j := hlt
          simp only [Fin.val_succ]
          omega
      · intro k
        by_cases hk : k=j
        · subst k
          have hz : w.count j=0 := List.count_eq_zero.mpr hjnot
          simp [hz]
        · simpa [List.count_append, hk, Ne.symm hk] using hcount k

end KLS.ConstantReduction

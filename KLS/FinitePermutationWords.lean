import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Tactic

/-! A quantitative adjacent-transposition factorization of every finite
permutation. The nonoptimal bound 2 q² is sufficient for a universal
exponential symmetrization constant. -/

open Equiv
namespace KLS

def adjacentFinSwap (n : ℕ) (i : Fin n) : Perm (Fin (n + 1)) :=
  Equiv.swap i.castSucc i.succ

theorem exists_adjacentFinSwapWord_of_lt {n : ℕ} (i j : Fin (n + 1)) (hij : i < j) :
    ∃ w : List (Fin n), (w.map (adjacentFinSwap n)).prod = Equiv.swap i j ∧
      w.length ≤ 2 * (j : ℕ) := by
  induction j using Fin.induction with
  | zero => exact False.elim (Fin.not_lt_zero i hij)
  | succ j ih =>
    obtain rfl | hlt := (Fin.le_castSucc_iff.mpr hij).eq_or_lt
    · refine ⟨[j], ?_, ?_⟩
      · simp [adjacentFinSwap]
      · simp only [List.length_singleton, Fin.val_succ]
        omega
    · obtain ⟨w, hw, hlen⟩ := ih hlt
      refine ⟨j :: (w ++ [j]), ?_, ?_⟩
      · rw [List.map_cons, List.map_append, List.prod_cons, List.prod_append,
          List.map_singleton, List.prod_singleton, hw, ← mul_assoc]
        exact (Equiv.swap_mul_swap_mul_swap hlt.ne hij.ne).trans (Equiv.swap_comm _ _)
      · simp only [List.length_cons, List.length_append, List.length_nil, Fin.val_succ]
        simp only [Fin.val_castSucc] at hlen
        omega

theorem exists_adjacentFinSwapWord_swap {n : ℕ} (i j : Fin (n + 1)) :
    ∃ w : List (Fin n), (w.map (adjacentFinSwap n)).prod = Equiv.swap i j ∧
      w.length ≤ 2 * n := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · obtain ⟨w, hw, hl⟩ := exists_adjacentFinSwapWord_of_lt i j hij
    exact ⟨w, hw, hl.trans (Nat.mul_le_mul_left 2 (Fin.is_le j))⟩
  · exact ⟨[], by simp only [List.map_nil, List.prod_nil, Equiv.swap_self]; rfl, by simp⟩
  · obtain ⟨w, hw, hl⟩ := exists_adjacentFinSwapWord_of_lt j i hji
    exact ⟨w, hw.trans (Equiv.swap_comm _ _), hl.trans (Nat.mul_le_mul_left 2 (Fin.is_le i))⟩

theorem swapFactorsAux_length_le {α : Type*} [DecidableEq α]
    (l : List α) (f : Perm α) (h : ∀ {x}, f x ≠ x → x ∈ l) :
    (Equiv.Perm.swapFactorsAux l f h).val.length ≤ l.length := by
  induction l generalizing f with
  | nil => simp [Equiv.Perm.swapFactorsAux]
  | cons x l ih =>
    unfold Equiv.Perm.swapFactorsAux
    split_ifs with hfx
    · exact (ih f (fun {y} hy => List.mem_of_ne_of_mem
        (fun hyx => by subst y; exact hy hfx.symm) (h hy))).trans (Nat.le_succ _)
    · exact Nat.succ_le_succ (ih (Equiv.swap x (f x) * f) (fun {y} hy =>
        have ht := Equiv.Perm.ne_and_ne_of_swap_mul_apply_ne_self hy
        List.mem_of_ne_of_mem ht.2 (h ht.1)))

theorem exists_swapWord_length_le_card {α : Type*} [Fintype α] [LinearOrder α]
    (f : Perm α) :
    ∃ l : List (Perm α), l.prod = f ∧ (∀ g ∈ l, Equiv.Perm.IsSwap g) ∧ l.length ≤ Fintype.card α := by
  let s := Equiv.Perm.swapFactorsAux (Finset.univ.toList : List α) f (fun {_} _ => by simp)
  refine ⟨s.val, s.prop.1, s.prop.2, ?_⟩
  have h := swapFactorsAux_length_le (Finset.univ.toList : List α) f (fun {_} _ => by simp)
  simpa only [Finset.length_toList, Finset.card_univ] using h

theorem exists_adjacentFinSwapWord_of_swap_list {n : ℕ} (l : List (Perm (Fin (n + 1))))
    (hl : ∀ g ∈ l, Equiv.Perm.IsSwap g) :
    ∃ w : List (Fin n), (w.map (adjacentFinSwap n)).prod = l.prod ∧
      w.length ≤ 2 * n * l.length := by
  induction l with
  | nil => exact ⟨[], by simp, by simp⟩
  | cons p l ih =>
    obtain ⟨i, j, _, hp⟩ := hl p (by simp)
    obtain ⟨v, hv, hvlen⟩ := exists_adjacentFinSwapWord_swap i j
    obtain ⟨w, hw, hwlen⟩ := ih (fun g hg => hl g (List.mem_cons_of_mem p hg))
    refine ⟨v ++ w, ?_, ?_⟩
    · rw [List.map_append, List.prod_append, hv, hw, List.prod_cons, hp]
    · simp only [List.length_append, List.length_cons]
      nlinarith

/-- Every permutation on q=n+1 positions has an adjacent-swap word of length
at most 2 n(n+1), hence at most 2 q². -/
theorem exists_adjacentFinSwapWord {n : ℕ} (f : Perm (Fin (n + 1))) :
    ∃ w : List (Fin n), (w.map (adjacentFinSwap n)).prod = f ∧
      w.length ≤ 2 * (n + 1) ^ 2 := by
  obtain ⟨l, hl, hs, hlen⟩ := exists_swapWord_length_le_card f
  obtain ⟨w, hw, hwlen⟩ := exists_adjacentFinSwapWord_of_swap_list l hs
  refine ⟨w, hw.trans hl, ?_⟩
  simp only [Fintype.card_fin] at hlen
  nlinarith

end KLS

#print axioms KLS.exists_adjacentFinSwapWord

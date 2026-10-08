import KLS.FinitePermutationWords
import Mathlib.GroupTheory.Perm.Fin

open Equiv
namespace KLS.ConstantReduction

theorem exists_adjacentFinSwapWord_of_lt_short {n : ℕ}
    (i j : Fin (n+1)) (hij : i < j) :
    ∃ w : List (Fin n), (w.map (adjacentFinSwap n)).prod = Equiv.swap i j ∧
      w.length ≤ 2*(j : ℕ)-1 := by
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
      · simp only [List.length_cons, List.length_append, List.length_nil,
          Fin.val_succ]
        simp only [Fin.val_castSucc] at hlen
        have hjpos : 0 < (j : ℕ) := by exact_mod_cast (Fin.zero_le i).trans_lt hlt
        omega

theorem exists_adjacentFinSwapWord_swap_zero {q : ℕ} (p : Fin (q+1)) :
    ∃ w : List (Fin q), (w.map (adjacentFinSwap q)).prod = Equiv.swap 0 p ∧
      w.length ≤ 2*q-1 := by
  by_cases hp : p = 0
  · subst p
    exact ⟨[], by simp only [List.map_nil, List.prod_nil, Equiv.swap_self]; rfl, by simp⟩
  · obtain ⟨w, hw, hlen⟩ := exists_adjacentFinSwapWord_of_lt_short 0 p
      (Fin.pos_iff_ne_zero.mpr hp)
    exact ⟨w, hw, hlen.trans (Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 (Fin.is_le p)) 1)⟩

def finSuccLiftHom (n : ℕ) : Equiv.Perm (Fin n) →* Equiv.Perm (Fin (n+1)) where
  toFun σ := Equiv.Perm.decomposeFin.symm (0, σ)
  map_one' := by
    simp only [Equiv.Perm.decomposeFin_symm_of_one, Equiv.swap_self]
    rfl
  map_mul' σ τ := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp

@[simp] theorem finSuccLiftHom_zero {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    finSuccLiftHom n σ 0 = 0 := by
  simp [finSuccLiftHom]

@[simp] theorem finSuccLiftHom_succ {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    finSuccLiftHom n σ i.succ = (σ i).succ := by
  simp [finSuccLiftHom]

theorem finSuccLiftHom_adjacent {q : ℕ} (i : Fin q) :
    finSuccLiftHom (q+1) (adjacentFinSwap q i) = adjacentFinSwap (q+1) i.succ := by
  apply Equiv.ext
  intro j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp only [finSuccLiftHom_zero, adjacentFinSwap]
    have h1 : (0 : Fin (q+1+1)) ≠ i.castSucc.succ := by
      intro h
      have hh := congrArg Fin.val h
      simp only [Fin.val_zero, Fin.val_succ, Fin.val_castSucc] at hh
      omega
    have h2 : (0 : Fin (q+1+1)) ≠ i.succ.succ := by
      intro h
      have hh := congrArg Fin.val h
      simp only [Fin.val_zero, Fin.val_succ] at hh
      omega
    exact (Equiv.swap_apply_of_ne_of_ne h1 h2).symm
  · rw [finSuccLiftHom_succ]
    exact (Fin.succ_injective (q+1)).map_swap i.castSucc i.succ k

theorem decomposeFin_eq_swap_mul_lift {n : ℕ} (p : Fin (n+1))
    (σ : Equiv.Perm (Fin n)) :
    Equiv.Perm.decomposeFin.symm (p, σ) = Equiv.swap 0 p * finSuccLiftHom n σ := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp

/-- Every permutation of q+1 positions has an actual adjacent-swap word
of length at most q², using the exact successive zero-position decomposition. -/
theorem exists_adjacentFinSwapWord_square {q : ℕ} (σ : Equiv.Perm (Fin (q+1))) :
    ∃ w : List (Fin q), (w.map (adjacentFinSwap q)).prod = σ ∧ w.length ≤ q^2 := by
  induction q with
  | zero =>
    have hσ : σ = 1 := by
      apply Equiv.ext
      intro i
      apply Fin.ext
      have hi := i.is_lt
      have hs := (σ i).is_lt
      simp only [Equiv.Perm.one_apply]
      omega
    subst σ
    exact ⟨[], by simp, by simp⟩
  | succ q ih =>
    let p := (Equiv.Perm.decomposeFin σ).1
    let τ := (Equiv.Perm.decomposeFin σ).2
    obtain ⟨w, hw, hwlen⟩ := ih τ
    obtain ⟨v, hv, hvlen⟩ := exists_adjacentFinSwapWord_swap_zero p
    have hlift : ((w.map Fin.succ).map (adjacentFinSwap (q+1))).prod =
        finSuccLiftHom (q+1) τ := by
      rw [List.map_map]
      calc
        _ = (w.map (fun i => finSuccLiftHom (q+1) (adjacentFinSwap q i))).prod := by
          congr 1
          apply List.map_congr_left
          intro i _
          exact (finSuccLiftHom_adjacent i).symm
        _ = finSuccLiftHom (q+1) (w.map (adjacentFinSwap q)).prod := by
          rw [map_list_prod, List.map_map]
          rfl
        _ = _ := by rw [hw]
    refine ⟨v ++ w.map Fin.succ, ?_, ?_⟩
    · rw [List.map_append, List.prod_append, hv, hlift,
        ← decomposeFin_eq_swap_mul_lift]
      exact Equiv.Perm.decomposeFin.symm_apply_apply σ
    · simp only [List.length_append, List.length_map]
      have hvlen' : v.length ≤ 2*q+1 := by omega
      nlinarith

end KLS.ConstantReduction

import KLS.LowerCumulantMultilinear

/-! Exact enumeration of labeled subsets containing the first slot. -/
open scoped BigOperators
noncomputable section
namespace KLS
variable {r : ℕ}

def tailSubset (S : Finset (Fin (r+1))) : Finset (Fin r) :=
  Finset.univ.filter fun i => i.succ ∈ S

def headSubset (T : Finset (Fin r)) : Finset (Fin (r+1)) :=
  insert 0 (T.map ⟨Fin.succ, by intro i j h; exact Fin.succ_inj.mp h⟩)

@[simp] theorem mem_tailSubset (S : Finset (Fin (r+1))) (i : Fin r) :
    i ∈ tailSubset S ↔ i.succ ∈ S := by simp [tailSubset]

@[simp] theorem zero_mem_headSubset (T : Finset (Fin r)) : (0 : Fin (r+1)) ∈ headSubset T := by
  simp [headSubset]

@[simp] theorem succ_mem_headSubset (T : Finset (Fin r)) (i : Fin r) :
    i.succ ∈ headSubset T ↔ i ∈ T := by
  simp only [headSubset, Finset.mem_insert, Fin.succ_ne_zero, false_or, Finset.mem_map]
  change (∃ a ∈ T, a.succ = i.succ) ↔ i ∈ T
  simp

@[simp] theorem tail_headSubset (T : Finset (Fin r)) : tailSubset (headSubset T) = T := by
  ext i
  simp

theorem head_tailSubset (S : Finset (Fin (r+1))) (hS : 0 ∈ S) : headSubset (tailSubset S) = S := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [hS]

@[simp] theorem card_headSubset (T : Finset (Fin r)) : (headSubset T).card = T.card+1 := by
  unfold headSubset
  rw [Finset.card_insert_of_notMem, Finset.card_map]
  intro h
  obtain ⟨i, _, hi⟩ := Finset.mem_map.mp h
  exact Fin.succ_ne_zero i hi

def headSubsetEquiv (r : ℕ) : Finset (Fin r) ≃ {S : Finset (Fin (r+1)) // 0 ∈ S} where
  toFun T := ⟨headSubset T, zero_mem_headSubset T⟩
  invFun S := tailSubset S.1
  left_inv := tail_headSubset
  right_inv S := Subtype.ext (head_tailSubset S.1 S.2)

theorem maskedDirections_headSubset {E : Type*} (u : E) (h : Fin r → E) (T : Finset (Fin r)) :
    maskedDirections (Fin.cons u h) (fun i => decide (i ∈ headSubset T)) =
      u :: maskedDirections h (fun i => decide (i ∈ T)) := by
  simp only [maskedDirections, zero_mem_headSubset, decide_true, ite_true,
    Fin.cons_zero, Fin.tail_def, Fin.cons_succ, succ_mem_headSubset]

theorem maskedDirections_headSubset_compl {E : Type*} (u : E) (h : Fin r → E) (T : Finset (Fin r)) :
    maskedDirections (Fin.cons u h) (fun i => decide (i ∈ (headSubset T)ᶜ)) =
      maskedDirections h (fun i => decide (i ∈ Tᶜ)) := by
  simp only [maskedDirections, Finset.mem_compl, zero_mem_headSubset, not_true_eq_false,
    decide_false, Bool.false_eq_true, ite_false, Fin.tail_def, Fin.cons_succ, succ_mem_headSubset]

end KLS
end

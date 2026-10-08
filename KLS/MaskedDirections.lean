import KLS.DirectionalWordLeibniz

/-! Labeled-subset combinatorics for the exact mixed Leibniz expansion. -/
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS
variable {E : Type*} {m : ℕ}

def maskSet (s : Fin m → Bool) : Finset (Fin m) := Finset.univ.filter (fun i => s i)

@[simp] theorem mem_maskSet (s : Fin m → Bool) (i : Fin m) :
    i ∈ maskSet s ↔ s i = true := by simp [maskSet]

def maskFinsetEquiv (m : ℕ) : (Fin m → Bool) ≃ Finset (Fin m) where
  toFun := maskSet
  invFun := fun S i => decide (i ∈ S)
  left_inv := by intro s; funext i; simp
  right_inv := by intro S; ext i; simp

@[simp] theorem maskSet_complement (s : Fin m → Bool) :
    maskSet (fun i => !(s i)) = (maskSet s)ᶜ := by
  ext i
  simp

theorem maskedDirections_length (h : Fin m → E) (s : Fin m → Bool) :
    (maskedDirections h s).length = (maskSet s).card := by
  rw [maskSet, Finset.card_filter]
  induction m with
  | zero => simp [maskedDirections]
  | succ m ih =>
    rw [Fin.sum_univ_succ]
    change (if s 0 then h 0 :: maskedDirections (Fin.tail h) (Fin.tail s)
      else maskedDirections (Fin.tail h) (Fin.tail s)).length = _
    have hh := ih (Fin.tail h) (Fin.tail s)
    simp only [Fin.tail_def] at hh ⊢
    rw [← hh]
    cases hs : s 0 <;> simp [hs, Nat.add_comm]

theorem maskedDirections_eq_nil_iff (h : Fin m → E) (s : Fin m → Bool) :
    maskedDirections h s = [] ↔ maskSet s = ∅ := by
  rw [← List.length_eq_zero_iff, maskedDirections_length, Finset.card_eq_zero]

theorem maskedDirections_all (h : Fin m → E) :
    maskedDirections h (fun _ => true) = List.ofFn h := by
  induction m with
  | zero => rfl
  | succ m ih => simp [maskedDirections, List.ofFn_succ, Fin.tail_def, ih]

theorem maskedDirections_none (h : Fin m → E) :
    maskedDirections h (fun _ => false) = [] := by
  induction m with
  | zero => rfl
  | succ m ih => simp [maskedDirections, Fin.tail_def, ih]

theorem maskedDirections_append_complement (h : Fin m → E) (s : Fin m → Bool) :
    (maskedDirections h s ++ maskedDirections h (fun i => !(s i))).Perm (List.ofFn h) := by
  induction m with
  | zero => simp [maskedDirections]
  | succ m ih =>
    rw [List.ofFn_succ]
    change ((if s 0 then h 0 :: maskedDirections (Fin.tail h) (Fin.tail s)
        else maskedDirections (Fin.tail h) (Fin.tail s)) ++
      (if !(s 0) then h 0 :: maskedDirections (Fin.tail h) (fun i => !(s i.succ))
        else maskedDirections (Fin.tail h) (fun i => !(s i.succ)))).Perm _
    cases hs : s 0
    · simp only [hs, Bool.false_eq_true, ↓reduceIte, Bool.not_false]
      exact List.perm_middle.trans ((ih (Fin.tail h) (Fin.tail s)).cons (h 0))
    · simp only [hs, ↓reduceIte, Bool.not_true, Bool.false_eq_true, List.cons_append]
      exact (ih (Fin.tail h) (Fin.tail s)).cons (h 0)

theorem maskedDirections_singleton (h : Fin m → E) (i : Fin m) :
    maskedDirections h (fun j => decide (j = i)) = [h i] := by
  induction m with
  | zero => exact i.elim0
  | succ m ih =>
    induction i using Fin.cases with
    | zero => simp [maskedDirections, maskedDirections_none, Fin.tail_def]
    | succ i =>
      have hzero : (0 : Fin (m+1)) ≠ i.succ := (Fin.succ_ne_zero i).symm
      simpa only [maskedDirections, hzero, decide_false, Bool.false_eq_true,
        ↓reduceIte, Fin.tail_def, Fin.succ_inj] using ih (Fin.tail h) i

theorem maskedDirections_complement_singleton (h : Fin m → E) (i : Fin m) :
    maskedDirections h (fun j => !(decide (j = i))) = (List.ofFn h).eraseIdx i.val := by
  induction m with
  | zero => exact i.elim0
  | succ m ih =>
    induction i using Fin.cases with
    | zero => simp [maskedDirections, maskedDirections_all, Fin.tail_def, List.ofFn_succ]
    | succ i =>
      have hzero : (0 : Fin (m+1)) ≠ i.succ := (Fin.succ_ne_zero i).symm
      simpa only [maskedDirections, hzero, decide_false, Bool.not_false,
        ↓reduceIte, Fin.tail_def, Fin.succ_inj, List.ofFn_succ, Fin.val_succ,
        List.eraseIdx_cons_succ] using congrArg (List.cons (h 0)) (ih (Fin.tail h) i)

end KLS
end
#print axioms KLS.maskedDirections_append_complement
#print axioms KLS.maskedDirections_length

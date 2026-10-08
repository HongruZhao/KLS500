import KLS.CanonicalLowerContraction
import Mathlib.Data.Fintype.Sort

/-! The recursive masks used in the cumulant drift enumerate precisely
their labeled subset; no unlabeled-subset multiplicities are discarded. -/
open scoped BigOperators
noncomputable section
namespace KLS
variable {E F : Type*} {m : ℕ}

theorem maskedDirections_map (f : E → F) (h : Fin m → E) (s : Fin m → Bool) :
    maskedDirections (fun i => f (h i)) s = (maskedDirections h s).map f := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [maskedDirections]
    split_ifs <;> simp only [List.map_cons, ← ih, Fin.tail_def]

theorem maskedDirections_sublist (h : Fin m → E) (s : Fin m → Bool) :
    (maskedDirections h s).Sublist (List.ofFn h) := by
  induction m with
  | zero => exact List.Sublist.refl _
  | succ m ih =>
    rw [List.ofFn_succ]
    change (if s 0 then h 0 :: maskedDirections (Fin.tail h) (Fin.tail s)
      else maskedDirections (Fin.tail h) (Fin.tail s)).Sublist _
    split_ifs
    · exact (ih (Fin.tail h) (Fin.tail s)).cons_cons _
    · exact (ih (Fin.tail h) (Fin.tail s)).cons _

theorem mem_maskedDirections (h : Fin m → E) (s : Fin m → Bool) (x : E) :
    x ∈ maskedDirections h s ↔ ∃ i, s i = true ∧ h i = x := by
  induction m with
  | zero => simp [maskedDirections]
  | succ m ih =>
    rw [Fin.exists_fin_succ]
    simp only [maskedDirections]
    split_ifs with hs
    · simp only [List.mem_cons, ih, Fin.tail_def, hs, true_and]
      tauto
    · simp only [ih, Fin.tail_def, hs, Bool.false_eq_true, false_and, false_or]

theorem maskedDirections_perm_orderEmb (h : Fin m → E) (S : Finset (Fin m)) :
    (maskedDirections h (fun i => decide (i ∈ S))).Perm
      (List.ofFn (fun i : Fin S.card => h (S.orderEmbOfFin rfl i))) := by
  have hn : (maskedDirections (fun i : Fin m => i) (fun i => decide (i ∈ S))).Nodup :=
    (List.nodup_ofFn.mpr Function.injective_id).sublist (maskedDirections_sublist _ _)
  have hn' : (List.ofFn (S.orderEmbOfFin rfl)).Nodup :=
    List.nodup_ofFn.mpr (S.orderEmbOfFin rfl).injective
  have hp : (maskedDirections (fun i : Fin m => i) (fun i => decide (i ∈ S))).Perm
      (List.ofFn (S.orderEmbOfFin rfl)) := by
    apply (List.perm_ext_iff_of_nodup hn hn').mpr
    intro i
    simp only [mem_maskedDirections, decide_eq_true_eq, List.mem_ofFn]
    constructor
    · rintro ⟨j, hj, rfl⟩
      obtain ⟨k, hk⟩ := (S.orderIsoOfFin rfl).surjective ⟨j, hj⟩
      exact ⟨k, congrArg Subtype.val hk⟩
    · rintro ⟨j, rfl⟩
      exact ⟨_, S.orderEmbOfFin_mem rfl j, rfl⟩
  have hh := hp.map h
  simpa only [← maskedDirections_map, List.map_ofFn, Function.comp_def] using hh

end KLS
end

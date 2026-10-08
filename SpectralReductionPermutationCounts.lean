import PermutationTriangularWord
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Count

/-! An actual adjacent-swap insertion word has both triangular length and
at most q occurrences of each of its q adjacent generators. -/
open Equiv
namespace KLS.ConstantReduction

theorem exists_adjacentFinSwapWord_send_zero_nodup {q : ℕ} (p : Fin (q+1)) :
    ∃ v : List (Fin q), (v.map (adjacentFinSwap q)).prod 0 = p ∧ v.length = (p : ℕ) ∧
      v.Nodup ∧ ∀ i ∈ v, (i : ℕ) < (p : ℕ) := by
  induction p using Fin.induction with
  | zero => exact ⟨[], by rfl, rfl, by simp, by simp⟩
  | succ i ih =>
    obtain ⟨v, hv, hlen, hnd, hsupport⟩ := ih
    refine ⟨i :: v, ?_, ?_, ?_, ?_⟩
    · rw [List.map_cons, List.prod_cons, Equiv.Perm.mul_apply, hv]
      simp [adjacentFinSwap]
    · simp only [List.length_cons, hlen, Fin.val_castSucc, Fin.val_succ]
    · apply List.nodup_cons.mpr
      refine ⟨?_, hnd⟩
      intro hi
      have hh := hsupport i hi
      simp only [Fin.val_castSucc] at hh
      omega
    · intro j hj
      simp only [List.mem_cons] at hj
      rcases hj with rfl | hj
      · simp
      · have hh := hsupport j hj
        simp only [Fin.val_castSucc, Fin.val_succ] at *
        omega

theorem exists_adjacentFinSwapWord_counted {q : ℕ} (σ : Equiv.Perm (Fin (q+1))) :
    ∃ w : List (Fin q), (w.map (adjacentFinSwap q)).prod = σ ∧
      2*w.length ≤ q*(q+1) ∧ ∀ i, w.count i ≤ q := by
  induction q with
  | zero =>
    obtain ⟨w, hw, hlen⟩ := exists_adjacentFinSwapWord_triangular σ
    refine ⟨w, hw, hlen, ?_⟩
    intro i
    exact Fin.elim0 i
  | succ q ih =>
    obtain ⟨v, hv, hvlen, hvnd, _⟩ := exists_adjacentFinSwapWord_send_zero_nodup (σ 0)
    let g : Equiv.Perm (Fin (q+1+1)) := (v.map (adjacentFinSwap (q+1))).prod
    let η := g⁻¹*σ
    have hη0 : η 0 = 0 := by
      change g⁻¹ (σ 0) = 0
      rw [← hv]
      change g.symm (g 0) = 0
      exact g.symm_apply_apply 0
    let τ := (Equiv.Perm.decomposeFin η).2
    have hp : (Equiv.Perm.decomposeFin η).1 = 0 := by
      have h := congrArg (fun e : Equiv.Perm (Fin (q+1+1)) => e 0)
        (Equiv.Perm.decomposeFin.symm_apply_apply η)
      change Equiv.Perm.decomposeFin.symm
        ((Equiv.Perm.decomposeFin η).1, (Equiv.Perm.decomposeFin η).2) 0 = η 0 at h
      rw [Equiv.Perm.decomposeFin_symm_apply_zero, hη0] at h
      exact h
    have hlift : finSuccLiftHom (q+1) τ = η := by
      change Equiv.Perm.decomposeFin.symm (0, τ) = η
      rw [← hp]
      exact Equiv.Perm.decomposeFin.symm_apply_apply η
    obtain ⟨w, hw, hwlen, hwcount⟩ := ih τ
    refine ⟨v ++ w.map Fin.succ, ?_, ?_, ?_⟩
    · rw [List.map_append, List.prod_append, finSuccLiftHom_word, hw, hlift]
      change g*(g⁻¹*σ) = σ
      simp
    · simp only [List.length_append, List.length_map]
      have hvbound : v.length ≤ q+1 := by rw [hvlen]; exact Fin.is_le (σ 0)
      nlinarith
    · intro i
      rw [List.count_append]
      refine Fin.cases ?_ (fun j => ?_) i
      · have hh : (w.map Fin.succ).count (0 : Fin (q+1)) = 0 := by
          apply List.count_eq_zero.mpr
          intro hz
          obtain ⟨j, _, hj⟩ := List.mem_map.mp hz
          exact Fin.succ_ne_zero j hj
        rw [hh]
        have hh' := (List.nodup_iff_count_le_one.mp hvnd) (0 : Fin (q+1))
        omega
      · rw [List.count_map_of_injective w Fin.succ (Fin.succ_injective q) j]
        have hh := hwcount j
        have hh' := (List.nodup_iff_count_le_one.mp hvnd) j.succ
        omega

end KLS.ConstantReduction

#print axioms KLS.ConstantReduction.exists_adjacentFinSwapWord_counted

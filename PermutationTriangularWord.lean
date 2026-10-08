import PermutationSquareWord

open Equiv
namespace KLS.ConstantReduction

/-- Moving the first point to any chosen image requires exactly that many
adjacent swaps. The remaining permutation is not prescribed. -/
theorem exists_adjacentFinSwapWord_send_zero {q : ℕ} (p : Fin (q+1)) :
    ∃ v : List (Fin q), (v.map (adjacentFinSwap q)).prod 0 = p ∧ v.length = (p : ℕ) := by
  induction p using Fin.induction with
  | zero => exact ⟨[], by rfl, rfl⟩
  | succ i ih =>
    obtain ⟨v, hv, hlen⟩ := ih
    refine ⟨i :: v, ?_, ?_⟩
    · rw [List.map_cons, List.prod_cons, Equiv.Perm.mul_apply, hv]
      simp [adjacentFinSwap]
    · simp only [List.length_cons, hlen, Fin.val_castSucc, Fin.val_succ]

theorem finSuccLiftHom_word {q : ℕ} (w : List (Fin q)) :
    ((w.map Fin.succ).map (adjacentFinSwap (q+1))).prod =
      finSuccLiftHom (q+1) (w.map (adjacentFinSwap q)).prod := by
  rw [List.map_map, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  exact (finSuccLiftHom_adjacent i).symm

/-- The optimal general maximum adjacent-word length, without importing a
Coxeter-length theorem: remove the image of zero and induct on its stabilizer. -/
theorem exists_adjacentFinSwapWord_triangular {q : ℕ} (σ : Equiv.Perm (Fin (q+1))) :
    ∃ w : List (Fin q), (w.map (adjacentFinSwap q)).prod = σ ∧
      2*w.length ≤ q*(q+1) := by
  induction q with
  | zero =>
    obtain ⟨w, hw, hlen⟩ := exists_adjacentFinSwapWord_square σ
    exact ⟨w, hw, by norm_num at hlen ⊢; omega⟩
  | succ q ih =>
    obtain ⟨v, hv, hvlen⟩ := exists_adjacentFinSwapWord_send_zero (σ 0)
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
    obtain ⟨w, hw, hwlen⟩ := ih τ
    refine ⟨v ++ w.map Fin.succ, ?_, ?_⟩
    · rw [List.map_append, List.prod_append, finSuccLiftHom_word, hw, hlift]
      change g*(g⁻¹*σ) = σ
      simp
    · simp only [List.length_append, List.length_map]
      have hvbound : v.length ≤ q+1 := by rw [hvlen]; exact Fin.is_le (σ 0)
      nlinarith

end KLS.ConstantReduction

import SpectralReductionPermutationCubic

/-! Keep the individual generator multiplicities and reverse the insertion
word so that the best weights align with the actual iteration scales. -/
open Equiv
open scoped BigOperators RealInnerProductSpace
noncomputable section
namespace KLS.ConstantReduction

theorem exists_adjacentFinSwapWord_individual {q : ℕ} (σ : Equiv.Perm (Fin (q+1))) :
    ∃ w : List (Fin q), (w.map (adjacentFinSwap q)).prod = σ ∧
      2*w.length ≤ q*(q+1) ∧ ∀ i, w.count i ≤ (i : ℕ)+1 := by
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
        simp only [Fin.val_zero]
        omega
      · rw [List.count_map_of_injective w Fin.succ (Fin.succ_injective q) j]
        have hh := hwcount j
        have hh' := (List.nodup_iff_count_le_one.mp hvnd) j.succ
        simp only [Fin.val_succ]
        omega


theorem adjacentFinSwap_reflection {q : ℕ} (i : Fin q) :
    (Fin.revPerm : Equiv.Perm (Fin (q+1))).permCongrHom (adjacentFinSwap q i) =
      adjacentFinSwap q i.rev := by
  change ((Fin.revPerm : Equiv.Perm (Fin (q+1))).symm.trans
    (Equiv.swap i.castSucc i.succ)).trans Fin.revPerm = _
  rw [Equiv.symm_trans_swap_trans]
  simp only [Fin.revPerm_apply, Fin.rev_castSucc, Fin.rev_succ, adjacentFinSwap]
  exact Equiv.swap_comm _ _

theorem exists_adjacentFinSwapWord_reverseCounted {q : ℕ} (σ : Equiv.Perm (Fin (q+1))) :
    ∃ w : List (Fin q), (w.map (adjacentFinSwap q)).prod = σ ∧
      2*w.length ≤ q*(q+1) ∧ ∀ i, w.count i ≤ q-(i : ℕ) := by
  let C := (Fin.revPerm : Equiv.Perm (Fin (q+1))).permCongrHom
  obtain ⟨w, hw, hlen, hcount⟩ := exists_adjacentFinSwapWord_individual (C σ)
  refine ⟨w.map Fin.rev, ?_, ?_, ?_⟩
  · have hCC : C (C σ)=σ := by
      apply Equiv.ext
      intro j
      change (Fin.revPerm.permCongr (Fin.revPerm.permCongr σ)) j = σ j
      simp only [Equiv.permCongr_apply, Fin.revPerm_apply, Fin.revPerm_symm, Fin.rev_rev]
    calc
      _ = (w.map (fun i => C (adjacentFinSwap q i))).prod := by
        simp only [List.map_map, Function.comp_def, C, adjacentFinSwap_reflection]
      _ = C ((w.map (adjacentFinSwap q)).prod) := by rw [map_list_prod, List.map_map]; rfl
      _ = σ := by rw [hw, hCC]
  · simpa only [List.length_map] using hlen
  · intro i
    have hh := List.count_map_of_injective w Fin.rev (Fin.rev_involutive.injective) i.rev
    simp only [Fin.rev_rev] at hh
    rw [hh]
    have hn := hcount i.rev
    rw [Fin.val_rev] at hn
    have hi := i.isLt
    omega

end KLS.ConstantReduction
end
#print axioms KLS.ConstantReduction.exists_adjacentFinSwapWord_reverseCounted

import OptMeanInsertionWords

/-! Reflection aligns the individual counts with the dyadic iteration while
preserving the exact mean word length. -/
open Equiv
open scoped BigOperators
noncomputable section
namespace KLS.ConstantReduction

theorem exists_adjacentFinSwapWords_mean_reverseCounted (q : ℕ) :
    ∃ W : Equiv.Perm (Fin (q+1)) → List (Fin q),
      (∀ σ, ((W σ).map (adjacentFinSwap q)).prod = σ ∧
        ∀ i, (W σ).count i ≤ q-(i : ℕ)) ∧
      4*(∑ σ, ((W σ).length : ℝ)) =
        (Fintype.card (Equiv.Perm (Fin (q+1))) : ℝ)*(q : ℝ)*(q+1) := by
  classical
  obtain ⟨W, hW, hmean⟩ := exists_adjacentFinSwapWords_mean_individual q
  let C := (Fin.revPerm : Equiv.Perm (Fin (q+1))).permCongrHom
  have hCC (σ : Equiv.Perm (Fin (q+1))) : C (C σ) = σ := by
    apply Equiv.ext
    intro j
    change (Fin.revPerm.permCongr (Fin.revPerm.permCongr σ)) j = σ j
    simp only [Equiv.permCongr_apply, Fin.revPerm_apply, Fin.revPerm_symm, Fin.rev_rev]
  let eC : Equiv.Perm (Fin (q+1)) ≃ Equiv.Perm (Fin (q+1)) :=
    ⟨C, C, hCC, hCC⟩
  refine ⟨fun σ => (W (C σ)).map Fin.rev, ?_, ?_⟩
  · intro σ
    constructor
    · calc
        _ = ((W (C σ)).map (fun i => C (adjacentFinSwap q i))).prod := by
          simp only [List.map_map, Function.comp_def, C, adjacentFinSwap_reflection]
        _ = C (((W (C σ)).map (adjacentFinSwap q)).prod) := by
          rw [map_list_prod, List.map_map]
          rfl
        _ = σ := by rw [(hW _).1, hCC]
    · intro i
      have hh := List.count_map_of_injective (W (C σ)) Fin.rev
        (Fin.rev_involutive.injective) i.rev
      simp only [Fin.rev_rev] at hh
      rw [hh]
      have hn := (hW (C σ)).2 i.rev
      rw [Fin.val_rev] at hn
      have hi := i.isLt
      omega
  · simp only [List.length_map]
    change 4*(∑ σ, ((W (eC σ)).length : ℝ)) = _
    rw [eC.sum_comp (fun σ => ((W σ).length : ℝ))]
    exact hmean

end KLS.ConstantReduction
end

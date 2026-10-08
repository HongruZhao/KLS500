import OptInsertionDecomposition

/-! Canonical adjacent words retain their individual generator counts and
have exactly half of the worst-case triangular length on average. -/
open Equiv
open scoped BigOperators
noncomputable section
namespace KLS.ConstantReduction

theorem twice_sum_fin_values (q : ℕ) :
    2*(∑ p : Fin (q+1), (p : ℝ)) = (q : ℝ)*(q+1) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.cast_add, Nat.cast_one]
    nlinarith

theorem exists_adjacentFinSwapWords_mean_individual (q : ℕ) :
    ∃ W : Equiv.Perm (Fin (q+1)) → List (Fin q),
      (∀ σ, ((W σ).map (adjacentFinSwap q)).prod = σ ∧
        ∀ i, (W σ).count i ≤ (i : ℕ)+1) ∧
      4*(∑ σ, ((W σ).length : ℝ)) =
        (Fintype.card (Equiv.Perm (Fin (q+1))) : ℝ)*(q : ℝ)*(q+1) := by
  classical
  induction q with
  | zero =>
    refine ⟨fun _ => [], ?_, ?_⟩
    · intro σ
      constructor
      · simp only [List.map_nil, List.prod_nil]
        apply Equiv.ext
        intro i
        apply Fin.ext
        have hi := i.isLt
        have hs := (σ i).isLt
        simp only [Equiv.Perm.one_apply]
        omega
      · intro i
        exact Fin.elim0 i
    · simp
  | succ q ih =>
    obtain ⟨W, hW, hmean⟩ := ih
    choose V hV hlen hnd hsupp using
      (fun p : Fin (q+1+1) => exists_adjacentFinSwapWord_send_zero_nodup p)
    let g : Fin (q+1+1) → Equiv.Perm (Fin (q+1+1)) :=
      fun p => ((V p).map (adjacentFinSwap (q+1))).prod
    have hg : ∀ p, g p 0 = p := hV
    let e := insertionDecomposition g hg
    let W' : (Fin (q+1+1) × Equiv.Perm (Fin (q+1))) → List (Fin (q+1)) :=
      fun v => V v.1 ++ (W v.2).map Fin.succ
    refine ⟨fun σ => W' (e σ), ?_, ?_⟩
    · intro σ
      constructor
      · change ((V (e σ).1 ++ (W (e σ).2).map Fin.succ).map _).prod = _
        rw [List.map_append, List.prod_append, finSuccLiftHom_word, (hW _).1]
        change e.symm (e σ) = σ
        exact e.symm_apply_apply σ
      · intro i
        change (V (e σ).1 ++ (W (e σ).2).map Fin.succ).count i ≤ _
        rw [List.count_append]
        refine Fin.cases ?_ (fun j => ?_) i
        · have hh : ((W (e σ).2).map Fin.succ).count (0 : Fin (q+1)) = 0 := by
            apply List.count_eq_zero.mpr
            intro hz
            obtain ⟨j, _, hj⟩ := List.mem_map.mp hz
            exact Fin.succ_ne_zero j hj
          rw [hh]
          have hh' := (List.nodup_iff_count_le_one.mp (hnd (e σ).1)) (0 : Fin (q+1))
          simp only [Fin.val_zero]
          omega
        · rw [List.count_map_of_injective (W (e σ).2) Fin.succ (Fin.succ_injective q) j]
          have hh := (hW (e σ).2).2 j
          have hh' := (List.nodup_iff_count_le_one.mp (hnd (e σ).1)) j.succ
          simp only [Fin.val_succ]
          omega
    · have hsum : (∑ σ, ((W' (e σ)).length : ℝ)) =
          (Fintype.card (Equiv.Perm (Fin (q+1))) : ℝ)*
            (∑ p : Fin (q+1+1), (p : ℝ)) +
          (q+2 : ℝ)*(∑ τ, ((W τ).length : ℝ)) := by
        rw [e.sum_comp (fun v => ((W' v).length : ℝ)), Fintype.sum_prod_type]
        simp only [W', List.length_append, List.length_map, Nat.cast_add, hlen,
          Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          Fintype.card_fin, Nat.cast_add, Nat.cast_one, ← Finset.mul_sum]
        ring
      have hcard : Fintype.card (Equiv.Perm (Fin (q+1+1))) =
          (q+2)*Fintype.card (Equiv.Perm (Fin (q+1))) := by
        rw [Fintype.card_congr e, Fintype.card_prod, Fintype.card_fin]
      have hcardR : (Fintype.card (Equiv.Perm (Fin (q+1+1))) : ℝ) =
          (q+2 : ℝ)*(Fintype.card (Equiv.Perm (Fin (q+1))) : ℝ) := by
        exact_mod_cast hcard
      have hp := twice_sum_fin_values (q+1)
      rw [hsum, hcardR]
      push_cast at hp ⊢
      nlinarith [congrArg (fun z : ℝ =>
        (Fintype.card (Equiv.Perm (Fin (q+1))) : ℝ)*z) hp,
        congrArg (fun z : ℝ => (q+2 : ℝ)*z) hmean]

end KLS.ConstantReduction
end

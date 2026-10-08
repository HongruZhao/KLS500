import OptInsertionJointDefinitions

/-! The insertion decomposition proves exact count and length-count moments
for one actual family of adjacent words representing every permutation. -/
open Equiv
open scoped BigOperators
noncomputable section
namespace KLS.ConstantReduction

theorem exists_adjacentFinSwapWords_joint_moments (q : ℕ) :
    ∃ W : Equiv.Perm (Fin (q+1)) → List (Fin q),
      (∀ σ, ((W σ).map (adjacentFinSwap q)).prod = σ) ∧
      (4*(∑ σ, ((W σ).length : ℝ)) =
        (Fintype.card (Equiv.Perm (Fin (q+1))) : ℝ)*(q : ℝ)*(q+1)) ∧
      (∀ i : Fin q, (∑ σ, ((W σ).count i : ℝ)) =
        (Fintype.card (Equiv.Perm (Fin (q+1))) : ℝ)*insertionMeanCount q i) ∧
      (∀ i : Fin q, (∑ σ, ((W σ).length : ℝ)*((W σ).count i : ℝ)) =
        (Fintype.card (Equiv.Perm (Fin (q+1))) : ℝ)*insertionJointMoment q i) := by
  classical
  induction q with
  | zero =>
    refine ⟨fun _ => [], ?_, by simp, ?_, ?_⟩
    · intro σ
      simp only [List.map_nil, List.prod_nil]
      apply Equiv.ext
      intro i
      apply Fin.ext
      have hi := i.isLt
      have hs := (σ i).isLt
      simp only [Equiv.Perm.one_apply]
      omega
    · intro i; exact Fin.elim0 i
    · intro i; exact Fin.elim0 i
  | succ q ih =>
    obtain ⟨W, hW, hmean, hcount, hjoint⟩ := ih
    choose V hV hlen hVcount using
      (fun p : Fin (q+1+1) => exists_adjacentFinSwapWord_send_zero_exact_counts p)
    let g : Fin (q+1+1) → Equiv.Perm (Fin (q+1+1)) :=
      fun p => ((V p).map (adjacentFinSwap (q+1))).prod
    have hg : ∀ p, g p 0 = p := hV
    let e := insertionDecomposition g hg
    let W' : (Fin (q+1+1) × Equiv.Perm (Fin (q+1))) → List (Fin (q+1)) :=
      fun v => V v.1 ++ (W v.2).map Fin.succ
    let N : ℝ := Fintype.card (Equiv.Perm (Fin (q+1)))
    let B (i : Fin (q+1)) (τ : Equiv.Perm (Fin (q+1))) : ℝ :=
      (((W τ).map Fin.succ).count i : ℝ)
    let C (i : Fin (q+1)) : ℝ :=
      if (i : ℕ) = 0 then 0 else insertionMeanCount q ((i : ℕ)-1)
    let J (i : Fin (q+1)) : ℝ :=
      if (i : ℕ) = 0 then 0 else insertionJointMoment q ((i : ℕ)-1)
    have hB (i : Fin (q+1)) : (∑ τ, B i τ) = N*C i := by
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [B, C, count_map_succ_zero]
      · simpa only [B, C, Fin.val_succ, Nat.add_one_ne_zero, ite_false,
          Nat.add_sub_cancel, List.count_map_of_injective _ Fin.succ (Fin.succ_injective q)]
          using hcount j
    have hJ (i : Fin (q+1)) :
        (∑ τ, ((W τ).length : ℝ)*B i τ) = N*J i := by
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [B, J, count_map_succ_zero]
      · simpa only [B, J, Fin.val_succ, Nat.add_one_ne_zero, ite_false,
          Nat.add_sub_cancel, List.count_map_of_injective _ Fin.succ (Fin.succ_injective q)]
          using hjoint j
    have hhead (p : Fin (q+1+1)) (i : Fin (q+1)) :
        ((V p).count i : ℝ) = if (i : ℕ) < (p : ℕ) then 1 else 0 := by
      simp only [hVcount, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    have hN : (Fintype.card (Equiv.Perm (Fin (q+1+1))) : ℝ) = (q+2 : ℝ)*N := by
      have hh : Fintype.card (Equiv.Perm (Fin (q+1+1))) =
          (q+2)*Fintype.card (Equiv.Perm (Fin (q+1))) := by
        rw [Fintype.card_congr e, Fintype.card_prod, Fintype.card_fin]
      dsimp only [N]
      exact_mod_cast hh
    have hp : (∑ p : Fin (q+1+1), (p : ℝ)) = (q+1 : ℝ)*(q+2)/2 := by
      have hh := twice_sum_fin_values (q+1)
      push_cast at hh
      nlinarith
    have hL : (∑ τ, ((W τ).length : ℝ)) = N*((q : ℝ)*(q+1)/4) := by
      change 4*(∑ τ, ((W τ).length : ℝ)) = N*(q : ℝ)*(q+1) at hmean
      nlinarith
    refine ⟨fun σ => W' (e σ), ?_, ?_, ?_, ?_⟩
    · intro σ
      change ((V (e σ).1 ++ (W (e σ).2).map Fin.succ).map _).prod = _
      rw [List.map_append, List.prod_append, finSuccLiftHom_word, hW]
      change e.symm (e σ) = σ
      exact e.symm_apply_apply σ
    · have hsum : (∑ σ, ((W' (e σ)).length : ℝ)) =
          N*(∑ p : Fin (q+1+1), (p : ℝ)) +
          (q+2 : ℝ)*(∑ τ, ((W τ).length : ℝ)) := by
        rw [e.sum_comp (fun v => ((W' v).length : ℝ)), Fintype.sum_prod_type]
        simp only [W', List.length_append, List.length_map, Nat.cast_add, hlen,
          Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          Fintype.card_fin, Nat.cast_add, Nat.cast_one, ← Finset.mul_sum]
        dsimp only [N]
        ring
      rw [hsum, hN, hp, hL]
      push_cast
      ring
    · intro i
      have hs : (∑ σ, ((W' (e σ)).count i : ℝ)) =
          N*(∑ p : Fin (q+1+1), if (i : ℕ) < (p : ℕ) then (1 : ℝ) else 0) +
          (q+2 : ℝ)*(∑ τ, B i τ) := by
        rw [e.sum_comp (fun v => ((W' v).count i : ℝ)), Fintype.sum_prod_type]
        simp only [W', List.count_append, Nat.cast_add, hhead,
          Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          Fintype.card_fin, Nat.cast_add, Nat.cast_one, ← Finset.mul_sum]
        dsimp only [N, B]
        ring
      rw [hs, insertionDigitCount_sum, hB, hN]
      simp only [insertionMeanCount]
      dsimp only [C]
      push_cast
      ring
    · intro i
      have heq : (∑ σ, ((W' (e σ)).length : ℝ)*((W' (e σ)).count i : ℝ)) =
          ∑ v : Fin (q+1+1) × Equiv.Perm (Fin (q+1)),
            ((v.1 : ℝ)+((W v.2).length : ℝ))*
              ((if (i : ℕ) < (v.1 : ℕ) then 1 else 0)+B i v.2) := by
        rw [e.sum_comp (fun v => ((W' v).length : ℝ)*((W' v).count i : ℝ))]
        simp only [W', List.length_append, List.length_map, List.count_append,
          Nat.cast_add, hlen, hhead, B]
      rw [heq, sum_product_add_moments
        (fun p : Fin (q+1+1) => (p : ℝ))
        (fun p : Fin (q+1+1) => if (i : ℕ) < (p : ℕ) then 1 else 0)
        (fun τ => ((W τ).length : ℝ)) (B i), insertionDigitJoint_sum,
        insertionDigitCount_sum, hp, hB, hJ, hL, hN]
      simp only [insertionJointMoment, Fintype.card_fin]
      change _ = (q+2 : ℝ)*N*(insertionDigitJoint (q+1) i +
        ((q : ℝ)*(q+1)/4)*insertionDigitCount (q+1) i +
        ((q+1 : ℝ)/2)*C i + J i)
      dsimp only [N]
      push_cast
      ring

end KLS.ConstantReduction
end

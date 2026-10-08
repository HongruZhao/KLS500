import TranspositionMeanDefects

/-! An elementary factor-two bound for the complete-transposition spectral
gap, proved by subgroup variance decomposition and full-group averaging. -/

open scoped BigOperators RealInnerProductSpace
noncomputable section
namespace KLS.ConstantReduction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem finiteIsometryAverage_eq_self_of_subsingleton
    {G : Type*} [Group G] [Fintype G] [Subsingleton G]
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) : finiteIsometryAverage ρ x=x := by
  have hg (g : G) : ρ g x=x := by rw [Subsingleton.elim g 1, map_one]; rfl
  have hN : (Fintype.card G : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  unfold finiteIsometryAverage
  simp only [hg, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hN, one_smul]

theorem completeTranspositionDefect_nonneg {I : Type*} [Fintype I] [DecidableEq I]
    (ρ : Equiv.Perm I →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    0 ≤ completeTranspositionDefect ρ x := by
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

theorem permutationAverage_completeTransposition_bound : ∀ n : ℕ,
    ∀ (ρ : Equiv.Perm (Fin n) →* (E ≃ₗᵢ[ℝ] E)) (x : E),
    (2*(n : ℝ))*‖x-finiteIsometryAverage ρ x‖ ^ 2 ≤ completeTranspositionDefect ρ x := by
  classical
  intro n
  induction n with
  | zero => intro ρ x; simpa using completeTranspositionDefect_nonneg ρ x
  | succ n ih =>
    intro ρ x
    by_cases hn : n=0
    · subst n
      have : Subsingleton (Equiv.Perm (Fin (0+1))) := ⟨fun σ τ => by
        apply Equiv.ext
        intro i
        apply Fin.ext
        have hs := (σ i).isLt
        have ht := (τ i).isLt
        omega⟩
      rw [finiteIsometryAverage_eq_self_of_subsingleton]
      simpa using completeTranspositionDefect_nonneg ρ x
    have hnR : (0 : ℝ)<n := by exact_mod_cast (show 0<n by omega)
    have hNR : (0 : ℝ)<n+1 := by positivity
    let V := ‖x-finiteIsometryAverage ρ x‖ ^ 2
    have hpoint (σ : Equiv.Perm (Fin (n+1))) :
        2*(n : ℝ)*(n+1)*V ≤
          (n+1 : ℝ)*completeTranspositionDefect (ρ.comp (finSuccLiftHom n)) (ρ σ x) +
          (n : ℝ)*starTranspositionDefect ρ (ρ σ x) 0 := by
      have hi := ih (ρ.comp (finSuccLiftHom n)) (ρ σ x)
      have hp := finiteIsometryAverage_subgroup_pythagoras ρ (finSuccLiftHom n) (ρ σ x)
      rw [permutationAverage_variance_action] at hp
      have hr := permutationAverage_subgroup_residual_eq_star ρ (ρ σ x)
      have hc := starDefect_subgroup_average_le ρ (finSuccLiftHom n)
        (fun h => finSuccLiftHom_zero h) (ρ σ x)
      have hres : (2*(n+1 : ℝ))*
          ‖finiteIsometryAverage (ρ.comp (finSuccLiftHom n)) (ρ σ x) -
            finiteIsometryAverage ρ (ρ σ x)‖ ^ 2 ≤ starTranspositionDefect ρ (ρ σ x) 0 := by
        rw [hr]
        calc
          _ = ∑ i : Fin (n+1),
              ‖finiteIsometryAverage (ρ.comp (finSuccLiftHom n)) (ρ σ x) -
                ρ (Equiv.swap 0 i) (finiteIsometryAverage (ρ.comp (finSuccLiftHom n)) (ρ σ x))‖ ^ 2 := by
            field_simp
          _ ≤ _ := hc
      have hi' := mul_le_mul_of_nonneg_left hi hNR.le
      have hr' := mul_le_mul_of_nonneg_left hres hnR.le
      have hp' := congrArg (fun z : ℝ => 2*(n : ℝ)*(n+1)*z) hp
      dsimp only [V]
      nlinarith
    have hs := Finset.sum_le_sum (s := Finset.univ) fun σ _ => hpoint σ
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hs
    have hs' := mul_le_mul_of_nonneg_left hs hNR.le
    have ht := sum_completeTranspositionDefect_subgroup_action ρ x
    have ht' := congrArg (fun z : ℝ => (n+1 : ℝ)*z) ht
    have ha := sum_starTranspositionDefect_action ρ x
    have ha' := congrArg (fun z : ℝ => (n : ℝ)*z) ha
    have htotal :
        (Fintype.card (Equiv.Perm (Fin (n+1))) : ℝ)*(2*(n : ℝ)*(n+1)^2*V) ≤
        (Fintype.card (Equiv.Perm (Fin (n+1))) : ℝ)*
          (((n : ℝ)*(n+1)-1)*completeTranspositionDefect ρ x) := by
      nlinarith
    have hcard : (0 : ℝ)<Fintype.card (Equiv.Perm (Fin (n+1))) := by
      exact_mod_cast Fintype.card_pos
    have hb := (mul_le_mul_iff_right₀ hcard).mp htotal
    have hT := completeTranspositionDefect_nonneg ρ x
    have hb' : 2*(n : ℝ)*(n+1)^2*V ≤
        ((n : ℝ)*(n+1))*completeTranspositionDefect ρ x := by
      exact hb.trans (mul_le_mul_of_nonneg_right (by linarith) hT)
    have heq : 2*(n : ℝ)*(n+1)^2*V = ((n : ℝ)*(n+1))*(2*(n+1)*V) := by ring
    rw [heq] at hb'
    have hh := (mul_le_mul_iff_right₀ (mul_pos hnR hNR)).mp hb'
    simpa only [Nat.cast_add, Nat.cast_one, V] using hh

theorem norm_sub_permutationAverage_sq_le_completeTranspositions {n : ℕ}
    (hn : 1≤n) (ρ : Equiv.Perm (Fin n) →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    ‖x-finiteIsometryAverage ρ x‖ ^ 2 ≤
      (2*(n : ℝ))⁻¹ * completeTranspositionDefect ρ x := by
  have hnR : (0 : ℝ)<2*(n : ℝ) := by exact_mod_cast (show 0<2*n by omega)
  have hh := permutationAverage_completeTransposition_bound n ρ x
  apply (le_inv_mul_iff₀ hnR).mpr
  exact hh

end KLS.ConstantReduction
end

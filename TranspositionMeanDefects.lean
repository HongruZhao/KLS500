import TranspositionDefectAlgebra

open scoped BigOperators RealInnerProductSpace
noncomputable section
namespace KLS.ConstantReduction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem permutationAverage_variance_action {I : Type*} [Fintype I] [DecidableEq I]
    (ρ : Equiv.Perm I →* (E ≃ₗᵢ[ℝ] E)) (x : E) (σ : Equiv.Perm I) :
    ‖ρ σ x-finiteIsometryAverage ρ (ρ σ x)‖ ^ 2 =
      ‖x-finiteIsometryAverage ρ x‖ ^ 2 := by
  rw [finiteIsometryAverage_right_invariant]
  rw [← finiteIsometryAverage_fixed ρ x σ, ← map_sub, LinearIsometryEquiv.norm_map]
  rw [finiteIsometryAverage_fixed]

theorem sum_starTranspositionDefect_action {n : ℕ}
    (ρ : Equiv.Perm (Fin (n+1)) →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    (n+1 : ℝ)*(∑ σ : Equiv.Perm (Fin (n+1)), starTranspositionDefect ρ (ρ σ x) 0) =
      (Fintype.card (Equiv.Perm (Fin (n+1))) : ℝ)*completeTranspositionDefect ρ x := by
  simp_rw [starTranspositionDefect_action]
  simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one,
    completeTranspositionDefect, starTranspositionDefect] using
      (perm_sum_eval_inv (starTranspositionDefect ρ x) (0 : Fin (n+1)))

theorem completeTranspositionDefect_split_zero {n : ℕ}
    (ρ : Equiv.Perm (Fin (n+1)) →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    completeTranspositionDefect ρ x =
      completeTranspositionDefect (ρ.comp (finSuccLiftHom n)) x +
      2*starTranspositionDefect ρ x 0 := by
  classical
  have hdiag : ‖x-ρ (Equiv.swap (0 : Fin (n+1)) 0) x‖ ^ 2=0 := by
    rw [Equiv.swap_self]
    change ‖x-ρ 1 x‖ ^ 2=0
    simp
  have hsym (i : Fin n) : ‖x-ρ (Equiv.swap i.succ 0) x‖ ^ 2 =
      ‖x-ρ (Equiv.swap 0 i.succ) x‖ ^ 2 := by rw [Equiv.swap_comm]
  unfold completeTranspositionDefect starTranspositionDefect
  simp only [MonoidHom.comp_apply, finSuccLiftHom_swap]
  rw [Fin.sum_univ_succ]
  simp_rw [Fin.sum_univ_succ]
  simp only [hdiag, zero_add, hsym, Finset.sum_add_distrib]
  ring

theorem sum_completeTranspositionDefect_subgroup_action {n : ℕ}
    (ρ : Equiv.Perm (Fin (n+1)) →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    (n+1 : ℝ)*(∑ σ : Equiv.Perm (Fin (n+1)),
      completeTranspositionDefect (ρ.comp (finSuccLiftHom n)) (ρ σ x)) =
      (n-1 : ℝ)*(Fintype.card (Equiv.Perm (Fin (n+1))) : ℝ)*
        completeTranspositionDefect ρ x := by
  have hs (σ : Equiv.Perm (Fin (n+1))) :
      completeTranspositionDefect (ρ.comp (finSuccLiftHom n)) (ρ σ x) =
        completeTranspositionDefect ρ x-2*starTranspositionDefect ρ (ρ σ x) 0 := by
    have hh := completeTranspositionDefect_split_zero ρ (ρ σ x)
    rw [completeTranspositionDefect_action] at hh
    linarith
  simp_rw [hs]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hh := sum_starTranspositionDefect_action ρ x
  nlinarith

end KLS.ConstantReduction
end

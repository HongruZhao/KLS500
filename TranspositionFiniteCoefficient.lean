import TranspositionAverageBound

/-! A finite-dimensional improvement retained by the subgroup averaging
argument, without asserting the sharp random-transposition gap. -/

open scoped BigOperators
noncomputable section
namespace KLS.ConstantReduction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem permutationAverage_completeTransposition_coefficient_step
    {n : ℕ} (hn : 1≤n) (a : ℝ)
    (hprev : ∀ (ρ : Equiv.Perm (Fin n) →* (E ≃ₗᵢ[ℝ] E)) (x : E),
      ‖x-finiteIsometryAverage ρ x‖^2 ≤ a*completeTranspositionDefect ρ x)
    (ρ : Equiv.Perm (Fin (n+1)) →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    ‖x-finiteIsometryAverage ρ x‖^2 ≤
      (((n-1 : ℝ)/(n+1))*a+1/(2*(n+1 : ℝ)^2))*completeTranspositionDefect ρ x := by
  let V := ‖x-finiteIsometryAverage ρ x‖^2
  have hNR : (0 : ℝ)<n+1 := by positivity
  have hpoint (σ : Equiv.Perm (Fin (n+1))) :
      (2*(n+1 : ℝ))*V ≤
        (2*(n+1 : ℝ))*a*completeTranspositionDefect
          (ρ.comp (finSuccLiftHom n)) (ρ σ x)+starTranspositionDefect ρ (ρ σ x) 0 := by
    have hi := hprev (ρ.comp (finSuccLiftHom n)) (ρ σ x)
    have hp := finiteIsometryAverage_subgroup_pythagoras ρ (finSuccLiftHom n) (ρ σ x)
    rw [permutationAverage_variance_action] at hp
    have hr := permutationAverage_subgroup_residual_eq_star ρ (ρ σ x)
    have hc := starDefect_subgroup_average_le ρ (finSuccLiftHom n)
      (fun h => finSuccLiftHom_zero h) (ρ σ x)
    have hres : (2*(n+1 : ℝ))*
        ‖finiteIsometryAverage (ρ.comp (finSuccLiftHom n)) (ρ σ x)-
          finiteIsometryAverage ρ (ρ σ x)‖^2 ≤ starTranspositionDefect ρ (ρ σ x) 0 := by
      rw [hr]
      calc
        _ = ∑ i : Fin (n+1),
            ‖finiteIsometryAverage (ρ.comp (finSuccLiftHom n)) (ρ σ x)-
              ρ (Equiv.swap 0 i) (finiteIsometryAverage (ρ.comp (finSuccLiftHom n)) (ρ σ x))‖^2 := by
          field_simp
        _ ≤ _ := hc
    have hi' := mul_le_mul_of_nonneg_left hi (show (0 : ℝ)≤2*(n+1) by positivity)
    dsimp only [V]
    nlinarith
  have hs := Finset.sum_le_sum (s:=Finset.univ) fun σ _ => hpoint σ
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Finset.sum_add_distrib, ←Finset.mul_sum] at hs
  have hs' := mul_le_mul_of_nonneg_left hs hNR.le
  have ht := sum_completeTranspositionDefect_subgroup_action ρ x
  have ht' := congrArg (fun z : ℝ => (2*(n+1 : ℝ))*a*z) ht
  have ha := sum_starTranspositionDefect_action ρ x
  have htotal :
      (Fintype.card (Equiv.Perm (Fin (n+1))) : ℝ)*(2*(n+1 : ℝ)^2*V) ≤
      (Fintype.card (Equiv.Perm (Fin (n+1))) : ℝ)*
        ((2*(n+1 : ℝ)*a*(n-1)+1)*completeTranspositionDefect ρ x) := by
    nlinarith
  have hcard : (0 : ℝ)<Fintype.card (Equiv.Perm (Fin (n+1))) := by
    exact_mod_cast Fintype.card_pos
  have hb := (mul_le_mul_iff_right₀ hcard).mp htotal
  have hden : (0 : ℝ)<2*(n+1)^2 := by positivity
  have hh : V ≤ ((2*(n+1 : ℝ)*a*(n-1)+1)*completeTranspositionDefect ρ x)/
      (2*(n+1 : ℝ)^2) := (le_div_iff₀ hden).mpr (by nlinarith [hb])
  convert hh using 1
  field_simp

def completeTranspositionCoefficient : ℕ → ℝ
  | 0 => 0
  | 1 => 0
  | n+2 => ((n : ℝ)/(n+2))*completeTranspositionCoefficient (n+1)+1/(2*(n+2 : ℝ)^2)

theorem permutationAverage_completeTransposition_finite_coefficient : ∀ n : ℕ,
    ∀ (ρ : Equiv.Perm (Fin n) →* (E ≃ₗᵢ[ℝ] E)) (x : E),
    ‖x-finiteIsometryAverage ρ x‖^2 ≤
      completeTranspositionCoefficient n*completeTranspositionDefect ρ x := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
    intro ρ x
    rw [finiteIsometryAverage_eq_self_of_subsingleton]
    simp [completeTranspositionCoefficient]
  | one =>
    intro ρ x
    rw [finiteIsometryAverage_eq_self_of_subsingleton]
    simp [completeTranspositionCoefficient]
  | more n _ ih =>
    intro ρ x
    have hh := permutationAverage_completeTransposition_coefficient_step
      (by omega : 1≤n+1) (completeTranspositionCoefficient (n+1)) ih ρ x
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_sub_cancel_right,
      add_assoc, show (1 : ℝ)+1=2 by norm_num, completeTranspositionCoefficient] using hh

end KLS.ConstantReduction
end

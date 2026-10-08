import TranspositionStarContraction

open scoped BigOperators RealInnerProductSpace
noncomputable section
namespace KLS.ConstantReduction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def completeTranspositionDefect {I : Type*} [Fintype I] [DecidableEq I]
    (ρ : Equiv.Perm I →* (E ≃ₗᵢ[ℝ] E)) (x : E) : ℝ :=
  ∑ i : I, ∑ j : I, ‖x-ρ (Equiv.swap i j) x‖ ^ 2

def starTranspositionDefect {I : Type*} [Fintype I] [DecidableEq I]
    (ρ : Equiv.Perm I →* (E ≃ₗᵢ[ℝ] E)) (x : E) (i : I) : ℝ :=
  ∑ j : I, ‖x-ρ (Equiv.swap i j) x‖ ^ 2

theorem transpositionDefect_action {I : Type*} [Fintype I] [DecidableEq I]
    (ρ : Equiv.Perm I →* (E ≃ₗᵢ[ℝ] E)) (x : E)
    (σ : Equiv.Perm I) (i j : I) :
    ‖ρ σ x-ρ (Equiv.swap i j) (ρ σ x)‖ ^ 2 =
      ‖x-ρ (Equiv.swap (σ⁻¹ i) (σ⁻¹ j)) x‖ ^ 2 := by
  have hp := Equiv.swap_mul_eq_mul_swap σ i j
  have ha : ρ (Equiv.swap i j) (ρ σ x) =
      ρ σ (ρ (Equiv.swap (σ⁻¹ i) (σ⁻¹ j)) x) := by
    change (ρ (Equiv.swap i j) * ρ σ) x =
      (ρ σ * ρ (Equiv.swap (σ⁻¹ i) (σ⁻¹ j))) x
    rw [← map_mul, ← map_mul, hp]
  rw [ha, ← map_sub, LinearIsometryEquiv.norm_map]

theorem starTranspositionDefect_action {I : Type*} [Fintype I] [DecidableEq I]
    (ρ : Equiv.Perm I →* (E ≃ₗᵢ[ℝ] E)) (x : E)
    (σ : Equiv.Perm I) (i : I) :
    starTranspositionDefect ρ (ρ σ x) i = starTranspositionDefect ρ x (σ⁻¹ i) := by
  unfold starTranspositionDefect
  simp_rw [transpositionDefect_action]
  exact Equiv.sum_comp σ⁻¹ (fun j => ‖x-ρ (Equiv.swap (σ⁻¹ i) j) x‖ ^ 2)

theorem completeTranspositionDefect_action {I : Type*} [Fintype I] [DecidableEq I]
    (ρ : Equiv.Perm I →* (E ≃ₗᵢ[ℝ] E)) (x : E) (σ : Equiv.Perm I) :
    completeTranspositionDefect ρ (ρ σ x) = completeTranspositionDefect ρ x := by
  change (∑ i, starTranspositionDefect ρ (ρ σ x) i) = ∑ i, starTranspositionDefect ρ x i
  simp_rw [starTranspositionDefect_action]
  exact Equiv.sum_comp σ⁻¹ (starTranspositionDefect ρ x)

theorem perm_sum_eval_inv {I : Type*} [Fintype I] [DecidableEq I]
    (f : I → ℝ) (a : I) :
    (Fintype.card I : ℝ) * (∑ σ : Equiv.Perm I, f (σ⁻¹ a)) =
      (Fintype.card (Equiv.Perm I) : ℝ) * ∑ i, f i := by
  classical
  have hs (b : I) : (∑ σ : Equiv.Perm I, f (σ⁻¹ b)) =
      ∑ σ : Equiv.Perm I, f (σ⁻¹ a) := by
    calc
      _ = ∑ σ : Equiv.Perm I, f (((Equiv.swap a b)*σ)⁻¹ b) :=
        (Equiv.sum_comp (Equiv.mulLeft (Equiv.swap a b)) (fun σ => f (σ⁻¹ b))).symm
      _ = _ := by simp only [mul_inv_rev, Equiv.swap_inv,
        Equiv.Perm.mul_apply, Equiv.swap_apply_right]
  calc
    _ = ∑ i : I, ∑ σ : Equiv.Perm I, f (σ⁻¹ i) := by
      simp_rw [hs]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = ∑ σ : Equiv.Perm I, ∑ i : I, f (σ⁻¹ i) := Finset.sum_comm
    _ = _ := by
      simp_rw [fun σ : Equiv.Perm I => Equiv.sum_comp σ⁻¹ f]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem finSuccLiftHom_swap {n : ℕ} (i j : Fin n) :
    finSuccLiftHom n (Equiv.swap i j) = Equiv.swap i.succ j.succ := by
  apply Equiv.ext
  intro k
  refine Fin.cases ?_ (fun l => ?_) k
  · rw [finSuccLiftHom_zero]
    exact (Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero i).symm
      (Fin.succ_ne_zero j).symm).symm
  · rw [finSuccLiftHom_succ]
    exact (Fin.succ_injective n).map_swap i j l

end KLS.ConstantReduction
end

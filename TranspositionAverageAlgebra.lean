import FiniteAverageHilbertVariance
import PermutationSquareWord
import Mathlib.Algebra.Order.Chebyshev

/-! Finite Hilbert averaging identities for an elementary complete-transposition
comparison. No numerical KLS conclusion is asserted in this module. -/

open scoped BigOperators RealInnerProductSpace
noncomputable section
namespace KLS.ConstantReduction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem norm_finite_mean_sq_le {I : Type*} [Fintype I] [Nonempty I] (v : I → E) :
    ‖(Fintype.card I : ℝ)⁻¹ • ∑ i, v i‖ ^ 2 ≤
      (Fintype.card I : ℝ)⁻¹ * ∑ i, ‖v i‖ ^ 2 := by
  classical
  have hN : (Fintype.card I : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hNp : 0 ≤ (Fintype.card I : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hn : ‖∑ i, v i‖ ≤ ∑ i, ‖v i‖ := norm_sum_le _ _
  have hs : ‖∑ i, v i‖ ^ 2 ≤ (∑ i, ‖v i‖) ^ 2 := by
    exact (sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans hn)).mpr hn
  have hc : (∑ i, ‖v i‖) ^ 2 ≤
      (Fintype.card I : ℝ) * ∑ i, ‖v i‖ ^ 2 := by
    simpa only [Finset.card_univ] using
      (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => ‖v i‖))
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hNp, mul_pow]
  calc
    _ ≤ ((Fintype.card I : ℝ)⁻¹) ^ 2 *
        ((Fintype.card I : ℝ) * ∑ i, ‖v i‖ ^ 2) := by
      exact mul_le_mul_of_nonneg_left (hs.trans hc) (sq_nonneg _)
    _ = _ := by field_simp

theorem norm_sub_finiteIsometryAverage_sq_eq_norm_difference
    {G : Type*} [Group G] [Fintype G]
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    ‖x-finiteIsometryAverage ρ x‖ ^ 2 =
      ‖x‖ ^ 2 - ‖finiteIsometryAverage ρ x‖ ^ 2 := by
  rw [norm_sub_sq_real, inner_finiteIsometryAverage_self]
  ring

theorem finiteIsometryAverage_subgroup_pythagoras
    {G H : Type*} [Group G] [Fintype G] [Group H] [Fintype H]
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (e : H →* G) (x : E) :
    ‖x-finiteIsometryAverage ρ x‖ ^ 2 =
      ‖x-finiteIsometryAverage (ρ.comp e) x‖ ^ 2 +
      ‖finiteIsometryAverage (ρ.comp e) x-finiteIsometryAverage ρ x‖ ^ 2 := by
  have hfull := norm_sub_finiteIsometryAverage_sq_eq_norm_difference ρ x
  have hsub := norm_sub_finiteIsometryAverage_sq_eq_norm_difference (ρ.comp e) x
  have hrem := norm_sub_finiteIsometryAverage_sq_eq_norm_difference ρ
    (finiteIsometryAverage (ρ.comp e) x)
  rw [finiteIsometryAverage_absorb] at hrem
  linarith

theorem permutationAverage_eq_star_average {n : ℕ}
    (ρ : Equiv.Perm (Fin (n+1)) →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    finiteIsometryAverage ρ x = (n+1 : ℝ)⁻¹ •
      ∑ i : Fin (n+1), ρ (Equiv.swap 0 i)
        (finiteIsometryAverage (ρ.comp (finSuccLiftHom n)) x) := by
  classical
  have hcard : Fintype.card (Equiv.Perm (Fin (n+1))) =
      (n+1)*Fintype.card (Equiv.Perm (Fin n)) := by
    rw [Fintype.card_congr Equiv.Perm.decomposeFin, Fintype.card_prod, Fintype.card_fin]
  have hcardR : (Fintype.card (Equiv.Perm (Fin (n+1))) : ℝ) =
      (n+1 : ℝ)*(Fintype.card (Equiv.Perm (Fin n)) : ℝ) := by
    exact_mod_cast hcard
  have hsum : (∑ σ : Equiv.Perm (Fin (n+1)), ρ σ x) =
      ∑ i : Fin (n+1), ∑ τ : Equiv.Perm (Fin n),
        ρ (Equiv.swap 0 i) (ρ (finSuccLiftHom n τ) x) := by
    rw [← Equiv.Perm.decomposeFin.symm.sum_comp (fun σ => ρ σ x),
      Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro τ _
    rw [decomposeFin_eq_swap_mul_lift, map_mul]
    rfl
  unfold finiteIsometryAverage
  rw [hcardR, hsum]
  simp only [map_smul, map_sum, MonoidHom.comp_apply]
  rw [← Finset.smul_sum, smul_smul, mul_inv_rev]
  congr 1
  ring

end KLS.ConstantReduction
end

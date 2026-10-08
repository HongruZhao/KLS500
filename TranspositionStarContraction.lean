import TranspositionStarVariance

open scoped BigOperators RealInnerProductSpace
noncomputable section
namespace KLS.ConstantReduction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem starDefect_subgroup_average_le {n : ℕ} {H : Type*} [Group H] [Fintype H]
    (ρ : Equiv.Perm (Fin (n+1)) →* (E ≃ₗᵢ[ℝ] E))
    (e : H →* Equiv.Perm (Fin (n+1))) (he : ∀ h, e h 0=0) (x : E) :
    (∑ i : Fin (n+1), ‖finiteIsometryAverage (ρ.comp e) x -
      ρ (Equiv.swap 0 i) (finiteIsometryAverage (ρ.comp e) x)‖ ^ 2) ≤
      ∑ i : Fin (n+1), ‖x-ρ (Equiv.swap 0 i) x‖ ^ 2 := by
  classical
  have hinv0 (h : H) : (e h)⁻¹ 0=0 := by
    have hh := (e h).symm_apply_apply 0
    rw [he] at hh
    exact hh
  have hdefect (h : H) (i : Fin (n+1)) :
      ‖ρ (e h) x-ρ (Equiv.swap 0 i) (ρ (e h) x)‖ ^ 2 =
        ‖x-ρ (Equiv.swap 0 ((e h)⁻¹ i)) x‖ ^ 2 := by
    have hperm : Equiv.swap 0 i * e h = e h * Equiv.swap 0 ((e h)⁻¹ i) := by
      rw [Equiv.swap_mul_eq_mul_swap, hinv0]
    have hact : ρ (Equiv.swap 0 i) (ρ (e h) x) =
        ρ (e h) (ρ (Equiv.swap 0 ((e h)⁻¹ i)) x) := by
      change (ρ (Equiv.swap 0 i) * ρ (e h)) x =
        (ρ (e h) * ρ (Equiv.swap 0 ((e h)⁻¹ i))) x
      rw [← map_mul, ← map_mul, hperm]
    rw [hact, ← map_sub, LinearIsometryEquiv.norm_map]
  have hmean (i : Fin (n+1)) :
      finiteIsometryAverage (ρ.comp e) x -
        ρ (Equiv.swap 0 i) (finiteIsometryAverage (ρ.comp e) x) =
      (Fintype.card H : ℝ)⁻¹ • ∑ h : H,
        (ρ (e h) x-ρ (Equiv.swap 0 i) (ρ (e h) x)) := by
    simp only [finiteIsometryAverage, MonoidHom.comp_apply, map_smul,
      map_sum, Finset.sum_sub_distrib, smul_sub]
  have hpoint (i : Fin (n+1)) :
      ‖finiteIsometryAverage (ρ.comp e) x -
        ρ (Equiv.swap 0 i) (finiteIsometryAverage (ρ.comp e) x)‖ ^ 2 ≤
      (Fintype.card H : ℝ)⁻¹ * ∑ h : H,
        ‖x-ρ (Equiv.swap 0 ((e h)⁻¹ i)) x‖ ^ 2 := by
    rw [hmean]
    simpa only [hdefect] using norm_finite_mean_sq_le
      (fun h : H => ρ (e h) x-ρ (Equiv.swap 0 i) (ρ (e h) x))
  calc
    _ ≤ ∑ i : Fin (n+1), (Fintype.card H : ℝ)⁻¹ * ∑ h : H,
        ‖x-ρ (Equiv.swap 0 ((e h)⁻¹ i)) x‖ ^ 2 :=
      Finset.sum_le_sum fun i _ => hpoint i
    _ = (Fintype.card H : ℝ)⁻¹ * ∑ h : H, ∑ i : Fin (n+1),
        ‖x-ρ (Equiv.swap 0 ((e h)⁻¹ i)) x‖ ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ = (Fintype.card H : ℝ)⁻¹ * ∑ h : H, ∑ i : Fin (n+1),
        ‖x-ρ (Equiv.swap 0 i) x‖ ^ 2 := by
      congr 1
      apply Finset.sum_congr rfl
      intro h _
      exact Equiv.sum_comp ((e h)⁻¹) (fun i => ‖x-ρ (Equiv.swap 0 i) x‖ ^ 2)
    _ = _ := by
      have hN : (Fintype.card H : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
        inv_mul_cancel₀ hN, one_mul]

end KLS.ConstantReduction
end

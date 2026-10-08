import OptMeanReflectedWords

/-! The exact mean insertion length halves the weighted adjacent-defect
constant for the actual Hilbert permutation average. -/
open scoped BigOperators RealInnerProductSpace
noncomputable section
namespace KLS.ConstantReduction

theorem norm_sub_permutationAverage_sq_le_mean_individual {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {q : ℕ}
    (ρ : Equiv.Perm (Fin (q+1)) →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    ‖x-finiteIsometryAverage ρ x‖^2 ≤
      ((q : ℝ)*(q+1 : ℝ)/8)*∑ i : Fin q,
        (q-(i : ℕ) : ℕ)*‖x-ρ (adjacentFinSwap q i) x‖^2 := by
  classical
  obtain ⟨W, hW, hmean⟩ := exists_adjacentFinSwapWords_mean_reverseCounted q
  let D : Fin q → ℝ := fun i => ‖x-ρ (adjacentFinSwap q i) x‖
  let S := ∑ i : Fin q, ((q-(i : ℕ) : ℕ) : ℝ)*(D i)^2
  have hpoint (σ : Equiv.Perm (Fin (q+1))) :
      ‖x-ρ σ x‖^2 ≤ ((W σ).length : ℝ)*S := by
    have hn : ‖x-ρ σ x‖ ≤ ((W σ).map D).sum := by
      simpa only [(hW σ).1] using
        (norm_sub_isometry_word_le_sum ρ (adjacentFinSwap q) x (W σ))
    have hsq := (sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans hn)).mpr hn
    have hcs : (((W σ).map D).sum)^2 ≤
        ((W σ).length : ℝ)*((W σ).map (fun i => (D i)^2)).sum := by
      simpa [List.map_map, Function.comp_def] using
        (Multiset.sq_sum_le_card_mul_sum_sq (((W σ).map D : List ℝ) : Multiset ℝ))
    have hsum : ((W σ).map (fun i => (D i)^2)).sum ≤ S := by
      rw [list_sum_map_eq_sum_count]
      exact Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_right (by exact_mod_cast (hW σ).2 i) (sq_nonneg _)
    exact (hsq.trans hcs).trans (mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _))
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun σ _ => hpoint σ
  rw [← Finset.sum_mul] at hsum
  have hN : (0 : ℝ) < Fintype.card (Equiv.Perm (Fin (q+1))) := by
    exact_mod_cast Fintype.card_pos
  rw [norm_sub_finiteIsometryAverage_sq_eq_average]
  have hh := mul_le_mul_of_nonneg_left hsum
    (inv_nonneg.mpr (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hN.le))
  apply hh.trans_eq
  change (2*(Fintype.card (Equiv.Perm (Fin (q+1))) : ℝ))⁻¹*
      ((∑ σ, ((W σ).length : ℝ))*S) = ((q : ℝ)*(q+1)/8)*S
  field_simp
  nlinarith [congrArg (fun z : ℝ => z*S) hmean]

end KLS.ConstantReduction
end

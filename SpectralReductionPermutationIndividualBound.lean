import SpectralReductionPermutationIndividual

/-! Individual generator counts yield a weighted adjacent-defect estimate. -/
open scoped BigOperators RealInnerProductSpace
noncomputable section
namespace KLS.ConstantReduction

theorem norm_sub_permutationAverage_sq_le_individual {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {q : ℕ}
    (ρ : Equiv.Perm (Fin (q+1)) →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    ‖x-finiteIsometryAverage ρ x‖^2 ≤
      ((q : ℝ)*(q+1 : ℝ)/4)*∑ i : Fin q, (q-(i : ℕ) : ℕ)*‖x-ρ (adjacentFinSwap q i) x‖^2 := by
  let D : Fin q → ℝ := fun i => ‖x-ρ (adjacentFinSwap q i) x‖
  let S := ∑ i : Fin q, ((q-(i : ℕ) : ℕ) : ℝ)*(D i)^2
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  have hpoint (σ : Equiv.Perm (Fin (q+1))) :
      ‖x-ρ σ x‖^2 ≤ ((q : ℝ)*(q+1 : ℝ)/2)*S := by
    obtain ⟨w, hw, hlen, hcount⟩ := exists_adjacentFinSwapWord_reverseCounted σ
    have hn : ‖x-ρ σ x‖ ≤ (w.map D).sum := by
      rw [← hw]
      exact norm_sub_isometry_word_le_sum ρ _ x w
    have hsq := (sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans hn)).mpr hn
    have hcs : ((w.map D).sum)^2 ≤ (w.length : ℝ)*(w.map (fun i => (D i)^2)).sum := by
      simpa [List.map_map, Function.comp_def] using
        (Multiset.sq_sum_le_card_mul_sum_sq ((w.map D : List ℝ) : Multiset ℝ))
    have hW : (w.map (fun i => (D i)^2)).sum ≤ S := by
      rw [list_sum_map_eq_sum_count]
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcount i) (sq_nonneg _)
    have hlenR : (w.length : ℝ) ≤ (q : ℝ)*(q+1 : ℝ)/2 := by
      have hh : 2*(w.length : ℝ) ≤ (q : ℝ)*(q+1 : ℝ) := by exact_mod_cast hlen
      linarith
    calc
      _ ≤ (w.length : ℝ)*(w.map (fun i => (D i)^2)).sum := hsq.trans hcs
      _ ≤ (w.length : ℝ)*S := mul_le_mul_of_nonneg_left hW (Nat.cast_nonneg _)
      _ ≤ ((q : ℝ)*(q+1 : ℝ)/2)*S :=
        mul_le_mul_of_nonneg_right hlenR hS
      _ = _ := by ring
  have hh := norm_sub_finiteIsometryAverage_sq_le_half_of_bounds ρ x hpoint
  convert hh using 1
  dsimp only [S, D]
  ring


end KLS.ConstantReduction
end
#print axioms KLS.ConstantReduction.norm_sub_permutationAverage_sq_le_individual

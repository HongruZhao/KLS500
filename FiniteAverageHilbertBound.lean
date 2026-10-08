import FiniteAverageHilbertVariance

open scoped BigOperators RealInnerProductSpace
noncomputable section
namespace KLS.ConstantReduction

theorem exists_adjacentFinSwapWord_quadratic {q : ℕ} (σ : Equiv.Perm (Fin (q+1))) :
    ∃ w : List (Fin q), (w.map (adjacentFinSwap q)).prod = σ ∧
      w.length ≤ 2*q*(q+1) := by
  obtain ⟨l, hl, hs, hlen⟩ := exists_swapWord_length_le_card σ
  obtain ⟨w, hw, hwlen⟩ := exists_adjacentFinSwapWord_of_swap_list l hs
  refine ⟨w, hw.trans hl, ?_⟩
  simp only [Fintype.card_fin] at hlen
  exact hwlen.trans (Nat.mul_le_mul_left (2*q) hlen)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A uniform squared bound on the orbit gives half that bound for the
distance to the invariant projection. -/
theorem norm_sub_finiteIsometryAverage_sq_le_half_of_bounds
    {G : Type*} [Group G] [Fintype G]
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) {B : ℝ}
    (hB : ∀ g, ‖x - ρ g x‖ ^ 2 ≤ B) :
    ‖x - finiteIsometryAverage ρ x‖ ^ 2 ≤ B/2 := by
  have hN : (Fintype.card G : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [norm_sub_finiteIsometryAverage_sq_eq_average]
  calc
    _ ≤ (2*(Fintype.card G : ℝ))⁻¹ * ((Fintype.card G : ℝ)*B) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
        (Finset.sum_le_sum (fun g (_ : g ∈ Finset.univ) => hB g))
    _ = B/2 := by field_simp

/-- Hilbert orthogonality and the actual adjacent word improve the generic
averaging coefficient, without changing the group action or defect norm. -/
theorem norm_sub_permutationAverage_sq_le_hilbert {q : ℕ}
    (ρ : Equiv.Perm (Fin (q+1)) →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    ‖x - finiteIsometryAverage ρ x‖ ^ 2 ≤
      2*(q : ℝ)^2*(q+1 : ℝ)^2*∑ i : Fin q, ‖x-ρ (adjacentFinSwap q i) x‖^2 := by
  let S := ∑ i : Fin q, ‖x-ρ (adjacentFinSwap q i) x‖^2
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hD (i : Fin q) : ‖x-ρ (adjacentFinSwap q i) x‖ ≤ Real.sqrt S := by
    apply (Real.le_sqrt (norm_nonneg _) hS).mpr
    exact Finset.single_le_sum (fun j _ => sq_nonneg ‖x-ρ (adjacentFinSwap q j) x‖)
      (Finset.mem_univ i)
  have hpoint (σ : Equiv.Perm (Fin (q+1))) :
      ‖x-ρ σ x‖^2 ≤ 4*(q : ℝ)^2*(q+1 : ℝ)^2*S := by
    obtain ⟨w, hw, hlen⟩ := exists_adjacentFinSwapWord_quadratic σ
    have hn : ‖x-ρ σ x‖ ≤ (2*(q : ℝ)*(q+1 : ℝ))*Real.sqrt S := by
      rw [← hw]
      apply (norm_sub_isometry_word_le ρ _ x hD w).trans
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg S)
      exact_mod_cast hlen
    have hs := (sq_le_sq₀ (norm_nonneg _)
      (show 0 ≤ 2*(q : ℝ)*(q+1 : ℝ)*Real.sqrt S by positivity)).mpr hn
    calc
      _ ≤ (2*(q : ℝ)*(q+1 : ℝ)*Real.sqrt S)^2 := hs
      _ = _ := by rw [mul_pow, Real.sq_sqrt hS]; ring
  have hh := norm_sub_finiteIsometryAverage_sq_le_half_of_bounds ρ x hpoint
  convert hh using 1
  dsimp only [S]
  ring

end KLS.ConstantReduction
end

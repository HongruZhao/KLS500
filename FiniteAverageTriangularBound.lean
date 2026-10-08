import FiniteAverageHilbertBound
import PermutationTriangularWord

open scoped BigOperators RealInnerProductSpace
noncomputable section
namespace KLS.ConstantReduction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The inversion-length bound and Hilbert projection identity give the
coefficient q²(q+1)²/8 for the actual permutation average. -/
theorem norm_sub_permutationAverage_sq_le_triangular {q : ℕ}
    (ρ : Equiv.Perm (Fin (q+1)) →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    ‖x - finiteIsometryAverage ρ x‖ ^ 2 ≤
      ((q : ℝ)^2*(q+1 : ℝ)^2/8)*
        ∑ i : Fin q, ‖x-ρ (adjacentFinSwap q i) x‖^2 := by
  let S := ∑ i : Fin q, ‖x-ρ (adjacentFinSwap q i) x‖^2
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hD (i : Fin q) : ‖x-ρ (adjacentFinSwap q i) x‖ ≤ Real.sqrt S := by
    apply (Real.le_sqrt (norm_nonneg _) hS).mpr
    exact Finset.single_le_sum (fun j _ => sq_nonneg ‖x-ρ (adjacentFinSwap q j) x‖)
      (Finset.mem_univ i)
  have hpoint (σ : Equiv.Perm (Fin (q+1))) :
      ‖x-ρ σ x‖^2 ≤ ((q : ℝ)^2*(q+1 : ℝ)^2/4)*S := by
    obtain ⟨w, hw, hlen⟩ := exists_adjacentFinSwapWord_triangular σ
    have hlenR : (w.length : ℝ) ≤ (q : ℝ)*(q+1 : ℝ)/2 := by
      have hh : 2*(w.length : ℝ) ≤ (q : ℝ)*(q+1 : ℝ) := by exact_mod_cast hlen
      linarith
    have hn : ‖x-ρ σ x‖ ≤ ((q : ℝ)*(q+1 : ℝ)/2)*Real.sqrt S := by
      rw [← hw]
      apply (norm_sub_isometry_word_le ρ _ x hD w).trans
      exact mul_le_mul_of_nonneg_right hlenR (Real.sqrt_nonneg S)
    have hs := (sq_le_sq₀ (norm_nonneg _)
      (show 0 ≤ (q : ℝ)*(q+1 : ℝ)/2*Real.sqrt S by positivity)).mpr hn
    calc
      _ ≤ ((q : ℝ)*(q+1 : ℝ)/2*Real.sqrt S)^2 := hs
      _ = _ := by rw [mul_pow, Real.sq_sqrt hS]; ring
  have hh := norm_sub_finiteIsometryAverage_sq_le_half_of_bounds ρ x hpoint
  convert hh using 1
  dsimp only [S]
  ring

end KLS.ConstantReduction
end

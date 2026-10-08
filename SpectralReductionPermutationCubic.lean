import SpectralReductionPermutationCounts
import FiniteAverageHilbertBound
import Mathlib.Algebra.Order.Chebyshev

/-! Weighted Cauchy-Schwarz along an actual insertion word gives a cubic
adjacent-transposition estimate for the literal Hilbert group average. -/
open scoped BigOperators RealInnerProductSpace
noncomputable section
namespace KLS.ConstantReduction

theorem list_sum_map_eq_sum_count {A : Type*} [Fintype A] [DecidableEq A]
    (w : List A) (f : A → ℝ) :
    (w.map f).sum = ∑ a : A, (w.count a : ℝ)*f a := by
  induction w with
  | nil => simp
  | cons a w ih =>
    have hc (b : A) : ((a::w).count b : ℝ) = (w.count b : ℝ) + if b=a then 1 else 0 := by
      by_cases h : b=a
      · subst b; simp
      · simp [h, Ne.symm h]
    simp only [List.map_cons, List.sum_cons, ih, hc, add_mul, Finset.sum_add_distrib]
    simp [add_comm]

theorem norm_sub_isometry_word_le_sum {E G A : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [Group G]
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (s : A → G) (x : E) (w : List A) :
    ‖x-ρ (w.map s).prod x‖ ≤ (w.map (fun a => ‖x-ρ (s a) x‖)).sum := by
  induction w with
  | nil => simp
  | cons a w ih =>
    simp only [List.map_cons, List.prod_cons, map_mul, LinearIsometryEquiv.coe_mul,
      Function.comp_apply, List.sum_cons]
    calc
      _ ≤ ‖x-ρ (s a) x‖ + ‖ρ (s a) x-ρ (s a) (ρ (w.map s).prod x)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ = ‖x-ρ (s a) x‖ + ‖x-ρ (w.map s).prod x‖ := by
        rw [← map_sub, (ρ (s a)).norm_map]
      _ ≤ _ := add_le_add le_rfl ih

theorem norm_sub_permutationAverage_sq_le_cubic {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {q : ℕ}
    (ρ : Equiv.Perm (Fin (q+1)) →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    ‖x-finiteIsometryAverage ρ x‖^2 ≤
      ((q : ℝ)^2*(q+1 : ℝ)/4)*∑ i : Fin q, ‖x-ρ (adjacentFinSwap q i) x‖^2 := by
  let D : Fin q → ℝ := fun i => ‖x-ρ (adjacentFinSwap q i) x‖
  let S := ∑ i : Fin q, (D i)^2
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hpoint (σ : Equiv.Perm (Fin (q+1))) :
      ‖x-ρ σ x‖^2 ≤ ((q : ℝ)^2*(q+1 : ℝ)/2)*S := by
    obtain ⟨w, hw, hlen, hcount⟩ := exists_adjacentFinSwapWord_counted σ
    have hn : ‖x-ρ σ x‖ ≤ (w.map D).sum := by
      rw [← hw]
      exact norm_sub_isometry_word_le_sum ρ _ x w
    have hsq := (sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans hn)).mpr hn
    have hcs : ((w.map D).sum)^2 ≤ (w.length : ℝ)*(w.map (fun i => (D i)^2)).sum := by
      simpa [List.map_map, Function.comp_def] using
        (Multiset.sq_sum_le_card_mul_sum_sq ((w.map D : List ℝ) : Multiset ℝ))
    have hW : (w.map (fun i => (D i)^2)).sum ≤ (q : ℝ)*S := by
      rw [list_sum_map_eq_sum_count]
      calc
        _ ≤ ∑ i : Fin q, (q : ℝ)*(D i)^2 := by
          apply Finset.sum_le_sum
          intro i _
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcount i) (sq_nonneg _)
        _ = _ := by rw [Finset.mul_sum]
    have hlenR : (w.length : ℝ) ≤ (q : ℝ)*(q+1 : ℝ)/2 := by
      have hh : 2*(w.length : ℝ) ≤ (q : ℝ)*(q+1 : ℝ) := by exact_mod_cast hlen
      linarith
    calc
      _ ≤ (w.length : ℝ)*(w.map (fun i => (D i)^2)).sum := hsq.trans hcs
      _ ≤ (w.length : ℝ)*((q : ℝ)*S) := mul_le_mul_of_nonneg_left hW (Nat.cast_nonneg _)
      _ ≤ ((q : ℝ)*(q+1 : ℝ)/2)*((q : ℝ)*S) :=
        mul_le_mul_of_nonneg_right hlenR (mul_nonneg (Nat.cast_nonneg _) hS)
      _ = _ := by ring
  have hh := norm_sub_finiteIsometryAverage_sq_le_half_of_bounds ρ x hpoint
  convert hh using 1
  dsimp only [S, D]
  ring

end KLS.ConstantReduction
end

#print axioms KLS.ConstantReduction.norm_sub_permutationAverage_sq_le_cubic

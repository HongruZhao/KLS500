import TranspositionIntervalWords
import SpectralReductionPermutationCubic

open scoped BigOperators
noncomputable section
namespace KLS.ConstantReduction

theorem transpositionDefect_le_interval_adjacentDefects {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {q : ℕ}
    (ρ : Equiv.Perm (Fin (q+1)) →* (E ≃ₗᵢ[ℝ] E)) (x : E)
    (i j : Fin (q+1)) (hij : i<j) :
    ‖x-ρ (Equiv.swap i j) x‖^2 ≤
      4*((j : ℕ)-(i : ℕ) : ℕ)*
        ∑ k : Fin q, if (i : ℕ)≤k ∧ (k : ℕ)<j then
          ‖x-ρ (adjacentFinSwap q k) x‖^2 else 0 := by
  classical
  let D : Fin q → ℝ := fun k => ‖x-ρ (adjacentFinSwap q k) x‖
  let S := ∑ k : Fin q, if (i : ℕ)≤k ∧ (k : ℕ)<j then (D k)^2 else 0
  have hS : 0≤S := Finset.sum_nonneg fun k _ => by split_ifs <;> positivity
  obtain ⟨w, hw, hlen, hsupp, hcount⟩ := exists_adjacentFinSwapWord_interval i j hij
  have hn : ‖x-ρ (Equiv.swap i j) x‖ ≤ (w.map D).sum := by
    rw [←hw]
    exact norm_sub_isometry_word_le_sum ρ _ x w
  have hsq := (sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans hn)).mpr hn
  have hcs : ((w.map D).sum)^2 ≤ (w.length : ℝ)*(w.map (fun k => (D k)^2)).sum := by
    simpa [List.map_map, Function.comp_def] using
      (Multiset.sq_sum_le_card_mul_sum_sq ((w.map D : List ℝ) : Multiset ℝ))
  have hW : (w.map (fun k => (D k)^2)).sum ≤ 2*S := by
    rw [list_sum_map_eq_sum_count]
    dsimp only [S]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k _
    by_cases hk : (i : ℕ)≤k ∧ (k : ℕ)<j
    · rw [ite_eq_left hk]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcount k) (sq_nonneg _)
    · rw [ite_eq_right hk]
      have hz : w.count k=0 := List.count_eq_zero.mpr (fun h => hk (hsupp k h))
      simp [hz]
  have hlenR : (w.length : ℝ) ≤ 2*(((j : ℕ)-(i : ℕ) : ℕ) : ℝ) := by
    exact_mod_cast (hlen.trans (Nat.sub_le _ _))
  calc
    _ ≤ (w.length : ℝ)*(w.map (fun k => (D k)^2)).sum := hsq.trans hcs
    _ ≤ (w.length : ℝ)*(2*S) := mul_le_mul_of_nonneg_left hW (Nat.cast_nonneg _)
    _ ≤ (2*(((j : ℕ)-(i : ℕ) : ℕ) : ℝ))*(2*S) :=
      mul_le_mul_of_nonneg_right hlenR (mul_nonneg (by norm_num) hS)
    _ = _ := by dsimp only [S,D]; ring

end KLS.ConstantReduction
end

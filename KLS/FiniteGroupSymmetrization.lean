import KLS.FinitePermutationWords
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Quantitative symmetrization for a genuine finite permutation action by
linear isometries. A short adjacent word and averaging give a squared norm
bound by four times q^4 times the sum of squared adjacent defects. -/

open scoped BigOperators
noncomputable section
namespace KLS
variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_sub_isometry_word_le {G A : Type*} [Group G]
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (s : A → G) (x : E) {D : ℝ}
    (hD : ∀ a, ‖x - ρ (s a) x‖ ≤ D) (w : List A) :
    ‖x - ρ (w.map s).prod x‖ ≤ (w.length : ℝ) * D := by
  induction w with
  | nil => simp
  | cons a w ih =>
    simp only [List.map_cons, List.prod_cons, map_mul, LinearIsometryEquiv.coe_mul,
      Function.comp_apply]
    calc
      _ ≤ ‖x - ρ (s a) x‖ + ‖ρ (s a) x - ρ (s a) (ρ (w.map s).prod x)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ = ‖x - ρ (s a) x‖ + ‖x - ρ (w.map s).prod x‖ := by
        rw [← map_sub, (ρ (s a)).norm_map]
      _ ≤ D + (w.length : ℝ) * D := add_le_add (hD a) ih
      _ = ((a :: w).length : ℝ) * D := by simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; ring

theorem norm_sub_permutation_le_adjacent_bound {q : ℕ}
    (ρ : Equiv.Perm (Fin (q + 1)) →* (E ≃ₗᵢ[ℝ] E)) (x : E) {D : ℝ}
    (hD0 : 0 ≤ D) (hD : ∀ i, ‖x - ρ (adjacentFinSwap q i) x‖ ≤ D)
    (σ : Equiv.Perm (Fin (q + 1))) :
    ‖x - ρ σ x‖ ≤ (2 * (q + 1 : ℝ) ^ 2) * D := by
  obtain ⟨w, hw, hlen⟩ := exists_adjacentFinSwapWord σ
  rw [← hw]
  apply (norm_sub_isometry_word_le ρ _ x hD w).trans
  apply mul_le_mul_of_nonneg_right _ hD0
  exact_mod_cast hlen

def finiteIsometryAverage {G : Type*} [Group G] [Fintype G]
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) : E :=
  (Fintype.card G : ℝ)⁻¹ • ∑ g : G, ρ g x

theorem finiteIsometryAverage_fixed {G : Type*} [Group G] [Fintype G]
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) (g : G) :
    ρ g (finiteIsometryAverage ρ x) = finiteIsometryAverage ρ x := by
  simp only [finiteIsometryAverage, map_smul, map_sum]
  congr 1
  have hm (h : G) : ρ g (ρ h x) = ρ (g * h) x := by rw [map_mul]; rfl
  simp_rw [hm]
  exact Equiv.sum_comp (Equiv.mulLeft g) (fun h => ρ h x)

theorem norm_sub_finiteIsometryAverage_le {G : Type*} [Group G] [Fintype G]
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) {B : ℝ}
    (hb : ∀ g, ‖x - ρ g x‖ ≤ B) : ‖x - finiteIsometryAverage ρ x‖ ≤ B := by
  have hN : (Fintype.card G : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hNp : 0 ≤ (Fintype.card G : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have he : x - finiteIsometryAverage ρ x =
      (Fintype.card G : ℝ)⁻¹ • ∑ g : G, (x - ρ g x) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul ℝ, smul_sub, smul_smul, inv_mul_cancel₀ hN, one_smul]
    rfl
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg hNp]
  calc
    _ ≤ (Fintype.card G : ℝ)⁻¹ * ∑ g : G, ‖x - ρ g x‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) hNp
    _ ≤ (Fintype.card G : ℝ)⁻¹ * ((Fintype.card G : ℝ) * B) := by
      apply mul_le_mul_of_nonneg_left _ hNp
      simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
        (Finset.sum_le_sum (fun g (_ : g ∈ Finset.univ) => hb g))
    _ = B := by rw [← mul_assoc, inv_mul_cancel₀ hN, one_mul]

/-- A quantitative averaging inequality for every genuine isometric action
of the permutation group on q+1 positions. -/
theorem norm_sub_permutationAverage_sq_le {q : ℕ}
    (ρ : Equiv.Perm (Fin (q + 1)) →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    ‖x - finiteIsometryAverage ρ x‖ ^ 2 ≤
      4 * (q + 1 : ℝ) ^ 4 * ∑ i : Fin q, ‖x - ρ (adjacentFinSwap q i) x‖ ^ 2 := by
  let S := ∑ i : Fin q, ‖x - ρ (adjacentFinSwap q i) x‖ ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hD (i : Fin q) : ‖x - ρ (adjacentFinSwap q i) x‖ ≤ Real.sqrt S := by
    apply (Real.le_sqrt (norm_nonneg _) hS).mpr
    exact Finset.single_le_sum (fun j _ => sq_nonneg ‖x - ρ (adjacentFinSwap q j) x‖)
      (Finset.mem_univ i)
  have hb : ‖x - finiteIsometryAverage ρ x‖ ≤ (2 * (q + 1 : ℝ) ^ 2) * Real.sqrt S :=
    norm_sub_finiteIsometryAverage_le ρ x (norm_sub_permutation_le_adjacent_bound ρ x
      (Real.sqrt_nonneg S) hD)
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by positivity) (Real.sqrt_nonneg S))).mpr hb
  calc
    _ ≤ ((2 * (q + 1 : ℝ) ^ 2) * Real.sqrt S) ^ 2 := hs
    _ = _ := by rw [mul_pow, Real.sq_sqrt hS]; ring

end KLS
end

#print axioms KLS.finiteIsometryAverage_fixed
#print axioms KLS.norm_sub_permutationAverage_sq_le

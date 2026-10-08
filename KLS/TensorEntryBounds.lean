import KLS.TensorMetricFirstWhitened

/-! Elementary finite-coordinate bounds for the actual tensor energy noise. -/
open Matrix
open scoped BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS.TensorEnergy
variable {n r : ℕ}

theorem abs_tensorSlot_le (s : Fin r) (H : Matrix (Fin n) (Fin n) ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hH : ∀ i j, |H i j| ≤ B) (a b : Fin r → Fin n) :
    |tensorSlot s H a b| ≤ B := by
  rw [tensorSlot_apply, abs_mul]
  have hp : |∏ j ∈ Finset.univ.erase s, (1 : Matrix (Fin n) (Fin n) ℝ) (a j) (b j)| ≤ 1 := by
    rw [Finset.abs_prod]
    apply Finset.prod_le_one₀
    · intro j _
      exact abs_nonneg _
    · intro j _
      simp only [Matrix.one_apply]
      split_ifs <;> norm_num
  exact (mul_le_mul hp (hH _ _) (abs_nonneg _) (by norm_num)).trans_eq (one_mul B)

theorem abs_tensorSlotSum_le (H : Matrix (Fin n) (Fin n) ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hH : ∀ i j, |H i j| ≤ B) (a b : Fin r → Fin n) :
    |tensorSlotSum H a b| ≤ (r : ℝ)*B := by
  unfold tensorSlotSum
  simp only [Matrix.sum_apply]
  calc
    _ ≤ ∑ s : Fin r, |tensorSlot s H a b| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _s : Fin r, B := Finset.sum_le_sum fun s _ => abs_tensorSlot_le s H B hB hH a b
    _ = _ := by simp

theorem abs_dotProduct_matrix_mulVec_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : ι → ℝ) (H : Matrix ι ι ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hH : ∀ a b, |H a b| ≤ B) :
    |T ⬝ᵥ (H *ᵥ T)| ≤ B * (Fintype.card ι : ℝ) * (T ⬝ᵥ T) := by
  change |∑ a, T a * ∑ b, H a b * T b| ≤ _
  simp only [Finset.mul_sum]
  calc
    _ ≤ ∑ a, ∑ b, |T a * (H a b * T b)| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ =>
        Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ a, ∑ b, B*((T a)^2+(T b)^2)/2 := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro b _
      rw [abs_mul, abs_mul]
      have htw : 2 * |T a| * |T b| ≤ (T a)^2+(T b)^2 := by
        nlinarith [sq_nonneg (|T a|-|T b|), sq_abs (T a), sq_abs (T b)]
      calc
        _ ≤ |T a| * (B * |T b|) := by gcongr; exact hH a b
        _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left htw hB]
    _ = _ := by
      simp only [mul_add, add_div, Finset.sum_add_distrib, Finset.sum_div,
        Finset.sum_mul, Finset.mul_sum, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, dotProduct, ← pow_two]
      ring_nf
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      ring

theorem abs_dotProduct_tensorSlotSum_le (T : (Fin r → Fin n) → ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (B : ℝ) (hB : 0 ≤ B) (hH : ∀ i j, |H i j| ≤ B) :
    |T ⬝ᵥ (tensorSlotSum H *ᵥ T)| ≤ (r : ℝ)*B*(n : ℝ)^r*(T ⬝ᵥ T) := by
  simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] using
    abs_dotProduct_matrix_mulVec_le T (tensorSlotSum H) ((r : ℝ)*B) (by positivity)
      (abs_tensorSlotSum_le H B hB hH)

theorem abs_two_dotProduct_le {ι : Type*} [Fintype ι] (T W : ι → ℝ) :
    |2*(T ⬝ᵥ W)| ≤ (1/2 : ℝ)*(T ⬝ᵥ T)+2*(W ⬝ᵥ W) := by
  have hp := two_dotProduct_le T W
  have hn := two_dotProduct_le T (-W)
  simp only [dotProduct_neg, neg_dotProduct, neg_neg] at hn
  exact abs_le.mpr ⟨by linarith, hp⟩

end KLS.TensorEnergy
end
#print axioms KLS.TensorEnergy.abs_dotProduct_tensorSlotSum_le

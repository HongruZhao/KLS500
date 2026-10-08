import KLS.FiniteTaylorSumBounds

/-! Summation of a pointwise Taylor doubling estimate, including its early
indices and the actual finite overlap of the shifted defect windows. -/
noncomputable section
open scoped BigOperators
namespace KLS

theorem finite_taylor_doubling_sum
    (f g χ : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k) (hχ : ∀ k, 0 ≤ χ k)
    {a b e c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (he : 0 ≤ e)
    (N d : ℕ) (hd : 1 ≤ d)
    (hbound : ∀ k, f k ≤ e)
    (hc : (∑ k ∈ Finset.range N, χ k) ≤ c)
    (hlate : ∀ k, 2 * d ≤ k + 1 → k < N →
      f k ≤ a * g (k - d) + b * ∑ i : Fin (2 * d - 1), χ (k - (2 * d - 1) + i)) :
    (∑ k ∈ Finset.range (N - d), f k) ≤
      a * (∑ k ∈ Finset.range (N - 2 * d), g k) +
      ((2 * d - 1 : ℕ) : ℝ) * e + b * ((2 * d - 1 : ℕ) : ℝ) * c := by
  have hc0 : 0 ≤ c := (Finset.sum_nonneg (fun k _ => hχ k)).trans hc
  have hg0 : 0 ≤ a * (∑ k ∈ Finset.range (N - 2 * d), g k) :=
    mul_nonneg ha (Finset.sum_nonneg (fun k _ => hg k))
  by_cases hq : 2 * d - 1 ≤ N - d
  · let L := N - d - (2 * d - 1)
    have hlen : (2 * d - 1) + L = N - d := by dsimp [L]; omega
    have hearly : (∑ k ∈ Finset.range (2 * d - 1), f k) ≤
        ((2 * d - 1 : ℕ) : ℝ) * e := by
      calc
        _ ≤ ∑ _k ∈ Finset.range (2 * d - 1), e := Finset.sum_le_sum (fun k _ => hbound k)
        _ = _ := by simp
    have hgs : (∑ j ∈ Finset.range L, g (d - 1 + j)) ≤
        ∑ k ∈ Finset.range (N - 2 * d), g k :=
      nonneg_sum_range_shift_le g hg (d - 1) L (N - 2 * d) (by dsimp [L]; omega)
    have hχs : (∑ j ∈ Finset.range L, ∑ i : Fin (2 * d - 1), χ (j + i)) ≤
        ((2 * d - 1 : ℕ) : ℝ) * c := by
      exact (nonneg_sum_shift_windows_le χ hχ L (2 * d - 1) N (by dsimp [L]; omega)).trans
        (mul_le_mul_of_nonneg_left hc (by positivity))
    have hlateSum : (∑ j ∈ Finset.range L, f (2 * d - 1 + j)) ≤
        a * (∑ k ∈ Finset.range (N - 2 * d), g k) +
        b * ((2 * d - 1 : ℕ) : ℝ) * c := by
      calc
        _ ≤ ∑ j ∈ Finset.range L,
            (a * g (d - 1 + j) + b * ∑ i : Fin (2 * d - 1), χ (j + i)) := by
          apply Finset.sum_le_sum
          intro j hj
          have hjL : j < L := Finset.mem_range.mp hj
          have hkN : 2 * d - 1 + j < N := by dsimp [L] at hjL; omega
          have hx := hlate (2 * d - 1 + j) (by omega) hkN
          simpa only [show 2 * d - 1 + j - d = d - 1 + j by omega,
            show 2 * d - 1 + j - (2 * d - 1) = j by omega] using hx
        _ = a * (∑ j ∈ Finset.range L, g (d - 1 + j)) +
            b * (∑ j ∈ Finset.range L, ∑ i : Fin (2 * d - 1), χ (j + i)) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        _ ≤ a * (∑ k ∈ Finset.range (N - 2 * d), g k) +
            b * (((2 * d - 1 : ℕ) : ℝ) * c) :=
          add_le_add (mul_le_mul_of_nonneg_left hgs ha) (mul_le_mul_of_nonneg_left hχs hb)
        _ = _ := by ring
    rw [← hlen, Finset.sum_range_add]
    linarith
  · have hcount : ((N - d : ℕ) : ℝ) ≤ ((2 * d - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : N - d ≤ 2 * d - 1)
    have hsum : (∑ k ∈ Finset.range (N - d), f k) ≤ ((2 * d - 1 : ℕ) : ℝ) * e := by
      calc
        _ ≤ ∑ _k ∈ Finset.range (N - d), e := Finset.sum_le_sum (fun k _ => hbound k)
        _ = ((N - d : ℕ) : ℝ) * e := by simp
        _ ≤ _ := mul_le_mul_of_nonneg_right hcount he
    have hx : 0 ≤ b * ((2 * d - 1 : ℕ) : ℝ) * c := by positivity
    linarith

end KLS
end

#print axioms KLS.finite_taylor_doubling_sum

import WeightedFiniteTaylorWindow

open scoped BigOperators
noncomputable section
namespace KLS.ConstantReduction

theorem finite_taylor_doubling_sum_long_weighted
    (f g χ : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k) (hχ : ∀ k, 0 ≤ χ k)
    {a b e c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (he : 0 ≤ e)
    (N d q : ℕ) (hd : 1 ≤ d) (hdq : d≤q) (w : Fin (q) → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hbound : ∀ k, f k ≤ e)
    (hc : (∑ k ∈ Finset.range N, χ k) ≤ c)
    (hlate : ∀ k, q ≤ k → k < N →
      f k ≤ a * g (k - d) + b * ∑ i : Fin (q), w i * χ (k - (q) + i)) :
    (∑ k ∈ Finset.range (N - d), f k) ≤
      a * (∑ k ∈ Finset.range (N - 2 * d), g k) +
      ((q : ℕ) : ℝ) * e + b * (∑ i, w i) * c := by
  have hc0 : 0 ≤ c := (Finset.sum_nonneg (fun k _ => hχ k)).trans hc
  have hg0 : 0 ≤ a * (∑ k ∈ Finset.range (N - 2 * d), g k) :=
    mul_nonneg ha (Finset.sum_nonneg (fun k _ => hg k))
  by_cases hq : q ≤ N - d
  · let L := N - d - (q)
    have hlen : (q) + L = N - d := by dsimp [L]; omega
    have hearly : (∑ k ∈ Finset.range (q), f k) ≤
        ((q : ℕ) : ℝ) * e := by
      calc
        _ ≤ ∑ _k ∈ Finset.range (q), e := Finset.sum_le_sum (fun k _ => hbound k)
        _ = _ := by simp
    have hgs : (∑ j ∈ Finset.range L, g (q - d + j)) ≤
        ∑ k ∈ Finset.range (N - 2 * d), g k :=
      nonneg_sum_range_shift_le g hg (q - d) L (N - 2 * d) (by dsimp [L]; omega)
    have hχs : (∑ j ∈ Finset.range L, ∑ i : Fin (q), w i * χ (j + i)) ≤
        (∑ i, w i) * c := by
      exact (nonneg_sum_weighted_shift_windows_le χ hχ w hw L N (by dsimp [L]; omega)).trans
        (mul_le_mul_of_nonneg_left hc (Finset.sum_nonneg (fun i _ => hw i)))
    have hlateSum : (∑ j ∈ Finset.range L, f (q + j)) ≤
        a * (∑ k ∈ Finset.range (N - 2 * d), g k) +
        b * (∑ i, w i) * c := by
      calc
        _ ≤ ∑ j ∈ Finset.range L,
            (a * g (q - d + j) + b * ∑ i : Fin (q), w i * χ (j + i)) := by
          apply Finset.sum_le_sum
          intro j hj
          have hjL : j < L := Finset.mem_range.mp hj
          have hkN : q + j < N := by dsimp [L] at hjL; omega
          have hx := hlate (q + j) (by omega) hkN
          simpa only [show q + j - d = q - d + j by omega,
            show q + j - (q) = j by omega] using hx
        _ = a * (∑ j ∈ Finset.range L, g (q - d + j)) +
            b * (∑ j ∈ Finset.range L, ∑ i : Fin (q), w i * χ (j + i)) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        _ ≤ a * (∑ k ∈ Finset.range (N - 2 * d), g k) +
            b * ((∑ i, w i) * c) :=
          add_le_add (mul_le_mul_of_nonneg_left hgs ha) (mul_le_mul_of_nonneg_left hχs hb)
        _ = _ := by ring
    rw [← hlen, Finset.sum_range_add]
    linarith
  · have hcount : ((N - d : ℕ) : ℝ) ≤ ((q : ℕ) : ℝ) := by exact_mod_cast (by omega : N - d ≤ q)
    have hsum : (∑ k ∈ Finset.range (N - d), f k) ≤ ((q : ℕ) : ℝ) * e := by
      calc
        _ ≤ ∑ _k ∈ Finset.range (N - d), e := Finset.sum_le_sum (fun k _ => hbound k)
        _ = ((N - d : ℕ) : ℝ) * e := by simp
        _ ≤ _ := mul_le_mul_of_nonneg_right hcount he
    have hx : 0 ≤ b * (∑ i, w i) * c :=
      mul_nonneg (mul_nonneg hb (Finset.sum_nonneg (fun i _ => hw i))) hc0
    linarith

end KLS.ConstantReduction
end

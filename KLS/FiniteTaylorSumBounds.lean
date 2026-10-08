import Mathlib

/-! Finite nonnegative sums needed to sum the actual Taylor recursion.
The window multiplicity estimate is proved by interchanging the two sums. -/
noncomputable section
open scoped BigOperators
namespace KLS

theorem nonneg_sum_range_shift_le (f : ℕ → ℝ) (hf : ∀ k, 0 ≤ f k)
    (s L N : ℕ) (h : s + L ≤ N) :
    ∑ j ∈ Finset.range L, f (s + j) ≤ ∑ j ∈ Finset.range N, f j := by
  have hp : 0 ≤ ∑ j ∈ Finset.range s, f j := Finset.sum_nonneg (fun j _ => hf j)
  have he := Finset.sum_range_add f s L
  have hm : (∑ j ∈ Finset.range (s + L), f j) ≤ ∑ j ∈ Finset.range N, f j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h) (fun j _ _ => hf j)
  linarith

/-- Every length-q window, with its genuine shifted indices, is counted at
most q times in the containing prefix. -/
theorem nonneg_sum_shift_windows_le (f : ℕ → ℝ) (hf : ∀ k, 0 ≤ f k)
    (L q N : ℕ) (h : L + q ≤ N) :
    (∑ j ∈ Finset.range L, ∑ i : Fin q, f (j + i)) ≤
      (q : ℝ) * ∑ k ∈ Finset.range N, f k := by
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ i : Fin q, ∑ k ∈ Finset.range N, f k := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [Nat.add_comm] using nonneg_sum_range_shift_le f hf i L N (by omega)
    _ = _ := by simp

end KLS
end

#print axioms KLS.nonneg_sum_range_shift_le
#print axioms KLS.nonneg_sum_shift_windows_le

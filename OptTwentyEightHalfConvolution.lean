import OptTwentyEightHalfWeights

/-! The second-cumulant deficit is retained in the full convolution.
This gives one uniform estimate for every rank at least thirty-five. -/
open scoped BigOperators
noncomputable section
namespace KLS

theorem twentyEightHalfRankConvolution_bound {r : ℕ} (hr : 35 ≤ r) :
    ((r-2 : ℕ) : ℝ) * twentyEightHalfRankConvolution r ≤ ((r : ℝ)+9/8)^2 := by
  have hprod (j : ℕ) (hj : j ∈ Finset.Icc 1 (r-2)) :
      twentyEightHalfIntegralWeight j * twentyEightHalfCumulantWeight (r-j) ≤
        1 + twentyEightHalfIntegralExcess j + twentyEightHalfCumulantExcess (r-j) -
          (if r-j = 2 then (1-(8000/139707 : ℝ)) else 0) := by
    have hj' := Finset.mem_Icc.mp hj
    by_cases hcomp : r-j = 2
    · have hjlarge : 33 ≤ j := by omega
      rw [twentyEightHalfIntegralWeight_large hjlarge,
        twentyEightHalfIntegralExcess_large (by omega : 18 ≤ j), hcomp]
      norm_num [twentyEightHalfCumulantWeight, twentyEightHalfCumulantExcess]
    · simp only [hcomp, ite_false, sub_zero]
      have hmul := mul_le_mul (twentyEightHalfIntegralWeight_le_one_add_excess j)
        (twentyEightHalfCumulantWeight_le_one_add_excess (r-j))
        (twentyEightHalfCumulantWeight_pos _).le
        (show 0 ≤ 1 + twentyEightHalfIntegralExcess j by
          have := twentyEightHalfIntegralExcess_nonneg j; linarith)
      apply hmul.trans_eq
      by_cases hjs : 18 ≤ j
      · rw [twentyEightHalfIntegralExcess_large hjs]
        ring
      · have hcs : 18 ≤ r-j := by omega
        rw [twentyEightHalfCumulantExcess_large hcs]
        ring
  have hfirst := sum_twentyEightHalfIntegralExcess_le (Finset.Icc 1 (r-2))
  have hsecond : (∑ j ∈ Finset.Icc 1 (r-2), twentyEightHalfCumulantExcess (r-j)) ≤ (21/10 : ℝ) := by
    have hinj : Set.InjOn (fun j : ℕ => r-j) (↑(Finset.Icc 1 (r-2)) : Set ℕ) := by
      intro a ha b hb he
      have ha' := Finset.mem_Icc.mp ha
      have hb' := Finset.mem_Icc.mp hb
      change r-a = r-b at he
      omega
    rw [← Finset.sum_image (g := fun j : ℕ => r-j) (f := twentyEightHalfCumulantExcess) hinj]
    exact sum_twentyEightHalfCumulantExcess_le _
  have hnegative : (∑ j ∈ Finset.Icc 1 (r-2),
      if r-j = 2 then (1-(8000/139707 : ℝ)) else 0) = 1-(8000/139707 : ℝ) := by
    rw [Finset.sum_eq_single (r-2)]
    · rw [show r-(r-2) = 2 by omega]
      simp
    · intro j hj hne
      have hj' := Finset.mem_Icc.mp hj
      have hc : r-j ≠ 2 := by omega
      simp [hc]
    · intro hn
      exfalso
      apply hn
      exact Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩
  have hsum : twentyEightHalfRankConvolution r ≤ ((r-2 : ℕ) : ℝ) + 25/4 := by
    unfold twentyEightHalfRankConvolution
    have hh := Finset.sum_le_sum hprod
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      nsmul_eq_mul, mul_one] at hh
    have hcard : (Finset.Icc 1 (r-2)).card = r-2 := by simp
    rw [hcard, hnegative] at hh
    linarith
  have hm := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg (α := ℝ) (r-2))
  rw [Nat.cast_sub (by omega : 2 ≤ r)] at hm ⊢
  norm_num only [Nat.cast_ofNat] at hm ⊢
  nlinarith

end KLS
end

import OptTwentySevenConvolutionFinite

/-! The second-cumulant deficit is retained in the full convolution.
This gives one uniform estimate for every rank at least thirty-five. -/
open scoped BigOperators
noncomputable section
namespace KLS

theorem twentySevenRankConvolution_bound_large {r : ℕ} (hr : 31 ≤ r) :
    ((r-2 : ℕ) : ℝ) * twentySevenRankConvolution r ≤ ((r : ℝ)+2)^2 := by
  have hprod (j : ℕ) (hj : j ∈ Finset.Icc 1 (r-2)) :
      twentySevenIntegralWeight j * twentySevenCumulantWeight (r-j) ≤
        1 + twentySevenIntegralExcess j + twentySevenCumulantExcess (r-j) -
          (if r-j = 2 then (1-(4000/31347 : ℝ)) else 0) := by
    have hj' := Finset.mem_Icc.mp hj
    by_cases hcomp : r-j = 2
    · have hjlarge : 16 ≤ j := by omega
      rw [twentySevenIntegralWeight_large hjlarge,
        twentySevenIntegralExcess_large (by omega : 16 ≤ j), hcomp]
      norm_num [twentySevenCumulantWeight, twentySevenCumulantExcess]
    · simp only [hcomp, ite_false, sub_zero]
      have hmul := mul_le_mul (twentySevenIntegralWeight_le_one_add_excess j)
        (twentySevenCumulantWeight_le_one_add_excess (r-j))
        (twentySevenCumulantWeight_pos _).le
        (show 0 ≤ 1 + twentySevenIntegralExcess j by
          have := twentySevenIntegralExcess_nonneg j; linarith)
      apply hmul.trans_eq
      by_cases hjs : 16 ≤ j
      · rw [twentySevenIntegralExcess_large hjs]
        ring
      · have hcs : 16 ≤ r-j := by omega
        rw [twentySevenCumulantExcess_large hcs]
        ring
  have hfirst := sum_twentySevenIntegralExcess_le (Finset.Icc 1 (r-2))
  have hsecond : (∑ j ∈ Finset.Icc 1 (r-2), twentySevenCumulantExcess (r-j)) ≤ (5/2 : ℝ) := by
    have hinj : Set.InjOn (fun j : ℕ => r-j) (↑(Finset.Icc 1 (r-2)) : Set ℕ) := by
      intro a ha b hb he
      have ha' := Finset.mem_Icc.mp ha
      have hb' := Finset.mem_Icc.mp hb
      change r-a = r-b at he
      omega
    rw [← Finset.sum_image (g := fun j : ℕ => r-j) (f := twentySevenCumulantExcess) hinj]
    exact sum_twentySevenCumulantExcess_le _
  have hnegative : (∑ j ∈ Finset.Icc 1 (r-2),
      if r-j = 2 then (1-(4000/31347 : ℝ)) else 0) = 1-(4000/31347 : ℝ) := by
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
  have hsum : twentySevenRankConvolution r ≤ ((r-2 : ℕ) : ℝ) + 8 := by
    unfold twentySevenRankConvolution
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

theorem twentySevenRankConvolution_bound {r : ℕ} (hr : 17 ≤ r) :
    ((r-2 : ℕ) : ℝ)*twentySevenRankConvolution r ≤ ((r : ℝ)+2)^2 := by
  by_cases hlarge : 31 ≤ r
  · exact twentySevenRankConvolution_bound_large hlarge
  · interval_cases r
    · exact twentySevenRankConvolution_bound_17
    · exact twentySevenRankConvolution_bound_18
    · exact twentySevenRankConvolution_bound_19
    · exact twentySevenRankConvolution_bound_20
    · exact twentySevenRankConvolution_bound_21
    · exact twentySevenRankConvolution_bound_22
    · exact twentySevenRankConvolution_bound_23
    · exact twentySevenRankConvolution_bound_24
    · exact twentySevenRankConvolution_bound_25
    · exact twentySevenRankConvolution_bound_26
    · exact twentySevenRankConvolution_bound_27
    · exact twentySevenRankConvolution_bound_28
    · exact twentySevenRankConvolution_bound_29
    · exact twentySevenRankConvolution_bound_30

end KLS
namespace KLS.RouteArithmetic

theorem twentySeven_root_allowance_square {r : ℕ} (hr : 17 ≤ r) :
    (13/125 : ℝ) * (((r-2 : ℕ) : ℝ) * ((43/2000 : ℝ)*(13/125)*twentySevenRankConvolution r) *
      (27) * (r : ℝ)^2) ≤ ((159/2000 : ℝ)*((r : ℝ)+2)*(r : ℝ))^2 := by
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (twentySevenRankConvolution_bound hr)
      (show 0 ≤ (43/2000 : ℝ)*(13/125)^2*(27) by norm_num)) (sq_nonneg (r : ℝ))
  have hnum : (43/2000 : ℝ)*(13/125)^2*(27) ≤ (159/2000)^2 := by norm_num
  have h' := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hnum (sq_nonneg ((r : ℝ)+2))) (sq_nonneg (r : ℝ))
  convert h.trans h' using 1 <;> ring

theorem twentySeven_cumulant_coefficient {r : ℕ} (hr : 17 ≤ r) :
    (((r+2 : ℕ) : ℝ) + 4*(r : ℝ)*((r : ℝ)-1)) * (13/125 : ℝ) +
      2*((159/2000 : ℝ)*((r : ℝ)+2))*(r : ℝ) ≤
        (43/2000 : ℝ)*(27)*(r : ℝ)^2 := by
  have hr' : (17 : ℝ) ≤ r := by exact_mod_cast hr
  push_cast
  nlinarith [sq_nonneg ((r : ℝ)-17)]

theorem twentySeven_integral_coefficient {r : ℕ} (hr : 17 ≤ r) :
    (((r+2 : ℕ) : ℝ) + 2*(r : ℝ)*(5*(r : ℝ)-2)) * (13/125 : ℝ) +
      2*((159/2000 : ℝ)*((r : ℝ)+2))*(r : ℝ) ≤
        (3/7 : ℝ)*(13/125)*(27)*(r : ℝ)^2 := by
  have hr' : (17 : ℝ) ≤ r := by exact_mod_cast hr
  push_cast
  nlinarith [sq_nonneg ((r : ℝ)-17)]

end KLS.RouteArithmetic
end

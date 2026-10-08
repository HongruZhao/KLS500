import OptEighteenFifthWeights

set_option maxRecDepth 8192

open scoped BigOperators
noncomputable section
namespace KLS

theorem eighteenFifthRankConvolution_bound {r : ℕ} (hr : 2 ≤ r) :
    ((r-2 : ℕ) : ℝ)*eighteenFifthRankConvolution r ≤ (r : ℝ)^2 := by
  have hprod (j : ℕ) (hj : j ∈ Finset.Icc 1 (r-2)) :
      eighteenFifthIntegralWeight j * eighteenFifthCumulantWeight (r-j) ≤
        1 + eighteenFifthIntegralExcess j := by
    calc
      _ ≤ eighteenFifthIntegralWeight j * 1 := mul_le_mul_of_nonneg_left
        (eighteenFifthCumulantWeight_le_one _) (eighteenFifthIntegralWeight_pos j).le
      _ ≤ _ := by simpa only [mul_one] using eighteenFifthIntegralWeight_le_one_add_excess j
  have hsum : eighteenFifthRankConvolution r ≤ ((r-2 : ℕ) : ℝ) + 4 := by
    have hh := Finset.sum_le_sum hprod
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one] at hh
    have hcard : (Finset.Icc 1 (r-2)).card = r-2 := by simp
    rw [hcard] at hh
    exact hh.trans (add_le_add le_rfl (sum_eighteenFifthIntegralExcess_le _))
  have hm := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg (α := ℝ) (r-2))
  rw [Nat.cast_sub hr] at hm ⊢
  norm_num only [Nat.cast_ofNat] at hm ⊢
  nlinarith

end KLS
namespace KLS.RouteArithmetic

theorem eighteenFifth_root_allowance_square {r : ℕ} (hr : 129 ≤ r) :
    (9/20 : ℝ) * (((r-2 : ℕ) : ℝ) * ((63/500 : ℝ)*(9/20)*eighteenFifthRankConvolution r) *
      (91/5) * (r : ℝ)^2) ≤ ((13629/20000 : ℝ)*(r : ℝ)*(r : ℝ))^2 := by
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (eighteenFifthRankConvolution_bound (by omega : 2 ≤ r))
      (show 0 ≤ (63/500 : ℝ)*(9/20)^2*(91/5) by norm_num)) (sq_nonneg (r : ℝ))
  have hnum : (63/500 : ℝ)*(9/20)^2*(91/5) ≤ (13629/20000)^2 := by norm_num
  have h' := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hnum (sq_nonneg (r : ℝ))) (sq_nonneg (r : ℝ))
  convert h.trans h' using 1 <;> ring

theorem eighteenFifth_cumulant_coefficient {r : ℕ} (hr : 129 ≤ r) :
    (2*(r : ℝ)^2+3*r-2) * (9/20 : ℝ) +
      2*((13629/20000 : ℝ)*(r : ℝ))*(r : ℝ) ≤
        (63/500 : ℝ)*(91/5)*(r : ℝ)^2 := by
  have hr' : (129 : ℝ) ≤ r := by exact_mod_cast hr
  nlinarith [sq_nonneg ((r : ℝ)-129)]

theorem eighteenFifth_integral_coefficient {r : ℕ} (hr : 129 ≤ r) :
    ((4*(211/100 : ℝ)-2)*(r : ℝ)^2+(8*(211/100 : ℝ)-5)*r-2) * (9/20 : ℝ) +
      2*((13629/20000 : ℝ)*(r : ℝ))*(r : ℝ) ≤
        (111/211 : ℝ)*(9/20)*(91/5)*(r : ℝ)^2 := by
  have hr' : (129 : ℝ) ≤ r := by exact_mod_cast hr
  nlinarith [sq_nonneg ((r : ℝ)-129)]

end KLS.RouteArithmetic
end

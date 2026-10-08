import OptRankSymmetric128Weights

set_option maxRecDepth 8192

set_option maxHeartbeats 16000000
noncomputable section
namespace KLS.RouteArithmetic

theorem rankSymmetric128Certificate_2 :
    (rankSymmetric128IntegralWeight (2-1) * rankSymmetric128Convolution 2 ≤ (rankSymmetric128RootAllowance 2)^2) ∧
    (((4*rankSymmetric128Parameter 2-2)*(2 : ℝ)^2+(8*rankSymmetric128Parameter 2-5)*2-2) * rankSymmetric128IntegralWeight (2-1) +
      2 * rankSymmetric128RootAllowance 2 * (2 : ℝ) ≤ rankSymmetric128Coercivity 2 * (2 : ℝ)^2 * rankSymmetric128IntegralWeight 2) ∧
    (3 ≤ 2 → ((2*(2 : ℝ)^2+3*2-2) * rankSymmetric128IntegralWeight (2-1) +
      2 * rankSymmetric128RootAllowance 2 * (2 : ℝ) ≤ (2 : ℝ)^2 * rankSymmetric128CumulantWeight 2)) := by
  norm_num [rankSymmetric128Coercivity, rankSymmetric128Convolution, rankSymmetric128CauchyWeight, Finset.sum_Icc_succ_top]

theorem rankSymmetric128Certificate_3 :
    (rankSymmetric128IntegralWeight (3-1) * rankSymmetric128Convolution 3 ≤ (rankSymmetric128RootAllowance 3)^2) ∧
    (((4*rankSymmetric128Parameter 3-2)*(3 : ℝ)^2+(8*rankSymmetric128Parameter 3-5)*3-2) * rankSymmetric128IntegralWeight (3-1) +
      2 * rankSymmetric128RootAllowance 3 * (3 : ℝ) ≤ rankSymmetric128Coercivity 3 * (3 : ℝ)^2 * rankSymmetric128IntegralWeight 3) ∧
    (3 ≤ 3 → ((2*(3 : ℝ)^2+3*3-2) * rankSymmetric128IntegralWeight (3-1) +
      2 * rankSymmetric128RootAllowance 3 * (3 : ℝ) ≤ (3 : ℝ)^2 * rankSymmetric128CumulantWeight 3)) := by
  norm_num [rankSymmetric128Coercivity, rankSymmetric128Convolution, rankSymmetric128CauchyWeight, Finset.sum_Icc_succ_top]

theorem rankSymmetric128Certificate_4 :
    (rankSymmetric128IntegralWeight (4-1) * rankSymmetric128Convolution 4 ≤ (rankSymmetric128RootAllowance 4)^2) ∧
    (((4*rankSymmetric128Parameter 4-2)*(4 : ℝ)^2+(8*rankSymmetric128Parameter 4-5)*4-2) * rankSymmetric128IntegralWeight (4-1) +
      2 * rankSymmetric128RootAllowance 4 * (4 : ℝ) ≤ rankSymmetric128Coercivity 4 * (4 : ℝ)^2 * rankSymmetric128IntegralWeight 4) ∧
    (3 ≤ 4 → ((2*(4 : ℝ)^2+3*4-2) * rankSymmetric128IntegralWeight (4-1) +
      2 * rankSymmetric128RootAllowance 4 * (4 : ℝ) ≤ (4 : ℝ)^2 * rankSymmetric128CumulantWeight 4)) := by
  norm_num [rankSymmetric128Coercivity, rankSymmetric128Convolution, rankSymmetric128CauchyWeight, Finset.sum_Icc_succ_top]

theorem rankSymmetric128Certificate_5 :
    (rankSymmetric128IntegralWeight (5-1) * rankSymmetric128Convolution 5 ≤ (rankSymmetric128RootAllowance 5)^2) ∧
    (((4*rankSymmetric128Parameter 5-2)*(5 : ℝ)^2+(8*rankSymmetric128Parameter 5-5)*5-2) * rankSymmetric128IntegralWeight (5-1) +
      2 * rankSymmetric128RootAllowance 5 * (5 : ℝ) ≤ rankSymmetric128Coercivity 5 * (5 : ℝ)^2 * rankSymmetric128IntegralWeight 5) ∧
    (3 ≤ 5 → ((2*(5 : ℝ)^2+3*5-2) * rankSymmetric128IntegralWeight (5-1) +
      2 * rankSymmetric128RootAllowance 5 * (5 : ℝ) ≤ (5 : ℝ)^2 * rankSymmetric128CumulantWeight 5)) := by
  norm_num [rankSymmetric128Coercivity, rankSymmetric128Convolution, rankSymmetric128CauchyWeight, Finset.sum_Icc_succ_top]

theorem rankSymmetric128Certificate_6 :
    (rankSymmetric128IntegralWeight (6-1) * rankSymmetric128Convolution 6 ≤ (rankSymmetric128RootAllowance 6)^2) ∧
    (((4*rankSymmetric128Parameter 6-2)*(6 : ℝ)^2+(8*rankSymmetric128Parameter 6-5)*6-2) * rankSymmetric128IntegralWeight (6-1) +
      2 * rankSymmetric128RootAllowance 6 * (6 : ℝ) ≤ rankSymmetric128Coercivity 6 * (6 : ℝ)^2 * rankSymmetric128IntegralWeight 6) ∧
    (3 ≤ 6 → ((2*(6 : ℝ)^2+3*6-2) * rankSymmetric128IntegralWeight (6-1) +
      2 * rankSymmetric128RootAllowance 6 * (6 : ℝ) ≤ (6 : ℝ)^2 * rankSymmetric128CumulantWeight 6)) := by
  norm_num [rankSymmetric128Coercivity, rankSymmetric128Convolution, rankSymmetric128CauchyWeight, Finset.sum_Icc_succ_top]

theorem rankSymmetric128Certificate_7 :
    (rankSymmetric128IntegralWeight (7-1) * rankSymmetric128Convolution 7 ≤ (rankSymmetric128RootAllowance 7)^2) ∧
    (((4*rankSymmetric128Parameter 7-2)*(7 : ℝ)^2+(8*rankSymmetric128Parameter 7-5)*7-2) * rankSymmetric128IntegralWeight (7-1) +
      2 * rankSymmetric128RootAllowance 7 * (7 : ℝ) ≤ rankSymmetric128Coercivity 7 * (7 : ℝ)^2 * rankSymmetric128IntegralWeight 7) ∧
    (3 ≤ 7 → ((2*(7 : ℝ)^2+3*7-2) * rankSymmetric128IntegralWeight (7-1) +
      2 * rankSymmetric128RootAllowance 7 * (7 : ℝ) ≤ (7 : ℝ)^2 * rankSymmetric128CumulantWeight 7)) := by
  norm_num [rankSymmetric128Coercivity, rankSymmetric128Convolution, rankSymmetric128CauchyWeight, Finset.sum_Icc_succ_top]

theorem rankSymmetric128Certificate_8 :
    (rankSymmetric128IntegralWeight (8-1) * rankSymmetric128Convolution 8 ≤ (rankSymmetric128RootAllowance 8)^2) ∧
    (((4*rankSymmetric128Parameter 8-2)*(8 : ℝ)^2+(8*rankSymmetric128Parameter 8-5)*8-2) * rankSymmetric128IntegralWeight (8-1) +
      2 * rankSymmetric128RootAllowance 8 * (8 : ℝ) ≤ rankSymmetric128Coercivity 8 * (8 : ℝ)^2 * rankSymmetric128IntegralWeight 8) ∧
    (3 ≤ 8 → ((2*(8 : ℝ)^2+3*8-2) * rankSymmetric128IntegralWeight (8-1) +
      2 * rankSymmetric128RootAllowance 8 * (8 : ℝ) ≤ (8 : ℝ)^2 * rankSymmetric128CumulantWeight 8)) := by
  norm_num [rankSymmetric128Coercivity, rankSymmetric128Convolution, rankSymmetric128CauchyWeight, Finset.sum_Icc_succ_top]

theorem rankSymmetric128Certificate_9 :
    (rankSymmetric128IntegralWeight (9-1) * rankSymmetric128Convolution 9 ≤ (rankSymmetric128RootAllowance 9)^2) ∧
    (((4*rankSymmetric128Parameter 9-2)*(9 : ℝ)^2+(8*rankSymmetric128Parameter 9-5)*9-2) * rankSymmetric128IntegralWeight (9-1) +
      2 * rankSymmetric128RootAllowance 9 * (9 : ℝ) ≤ rankSymmetric128Coercivity 9 * (9 : ℝ)^2 * rankSymmetric128IntegralWeight 9) ∧
    (3 ≤ 9 → ((2*(9 : ℝ)^2+3*9-2) * rankSymmetric128IntegralWeight (9-1) +
      2 * rankSymmetric128RootAllowance 9 * (9 : ℝ) ≤ (9 : ℝ)^2 * rankSymmetric128CumulantWeight 9)) := by
  norm_num [rankSymmetric128Coercivity, rankSymmetric128Convolution, rankSymmetric128CauchyWeight, Finset.sum_Icc_succ_top]

end KLS.RouteArithmetic
end

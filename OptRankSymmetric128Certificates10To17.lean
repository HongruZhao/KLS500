import OptRankSymmetric128Weights

set_option maxRecDepth 8192

set_option maxHeartbeats 16000000
noncomputable section
namespace KLS.RouteArithmetic

theorem rankSymmetric128Certificate_10 :
    (rankSymmetric128IntegralWeight (10-1) * rankSymmetric128Convolution 10 ≤ (rankSymmetric128RootAllowance 10)^2) ∧
    (((4*rankSymmetric128Parameter 10-2)*(10 : ℝ)^2+(8*rankSymmetric128Parameter 10-5)*10-2) * rankSymmetric128IntegralWeight (10-1) +
      2 * rankSymmetric128RootAllowance 10 * (10 : ℝ) ≤ rankSymmetric128Coercivity 10 * (10 : ℝ)^2 * rankSymmetric128IntegralWeight 10) ∧
    (3 ≤ 10 → ((2*(10 : ℝ)^2+3*10-2) * rankSymmetric128IntegralWeight (10-1) +
      2 * rankSymmetric128RootAllowance 10 * (10 : ℝ) ≤ (10 : ℝ)^2 * rankSymmetric128CumulantWeight 10)) := by
  norm_num [rankSymmetric128Coercivity, rankSymmetric128Convolution, rankSymmetric128CauchyWeight, Finset.sum_Icc_succ_top]

theorem rankSymmetric128Certificate_11 :
    (rankSymmetric128IntegralWeight (11-1) * rankSymmetric128Convolution 11 ≤ (rankSymmetric128RootAllowance 11)^2) ∧
    (((4*rankSymmetric128Parameter 11-2)*(11 : ℝ)^2+(8*rankSymmetric128Parameter 11-5)*11-2) * rankSymmetric128IntegralWeight (11-1) +
      2 * rankSymmetric128RootAllowance 11 * (11 : ℝ) ≤ rankSymmetric128Coercivity 11 * (11 : ℝ)^2 * rankSymmetric128IntegralWeight 11) ∧
    (3 ≤ 11 → ((2*(11 : ℝ)^2+3*11-2) * rankSymmetric128IntegralWeight (11-1) +
      2 * rankSymmetric128RootAllowance 11 * (11 : ℝ) ≤ (11 : ℝ)^2 * rankSymmetric128CumulantWeight 11)) := by
  norm_num [rankSymmetric128Coercivity, rankSymmetric128Convolution, rankSymmetric128CauchyWeight, Finset.sum_Icc_succ_top]

theorem rankSymmetric128Certificate_12 :
    (rankSymmetric128IntegralWeight (12-1) * rankSymmetric128Convolution 12 ≤ (rankSymmetric128RootAllowance 12)^2) ∧
    (((4*rankSymmetric128Parameter 12-2)*(12 : ℝ)^2+(8*rankSymmetric128Parameter 12-5)*12-2) * rankSymmetric128IntegralWeight (12-1) +
      2 * rankSymmetric128RootAllowance 12 * (12 : ℝ) ≤ rankSymmetric128Coercivity 12 * (12 : ℝ)^2 * rankSymmetric128IntegralWeight 12) ∧
    (3 ≤ 12 → ((2*(12 : ℝ)^2+3*12-2) * rankSymmetric128IntegralWeight (12-1) +
      2 * rankSymmetric128RootAllowance 12 * (12 : ℝ) ≤ (12 : ℝ)^2 * rankSymmetric128CumulantWeight 12)) := by
  norm_num [rankSymmetric128Coercivity, rankSymmetric128Convolution, rankSymmetric128CauchyWeight, Finset.sum_Icc_succ_top]

theorem rankSymmetric128Certificate_13 :
    (rankSymmetric128IntegralWeight (13-1) * rankSymmetric128Convolution 13 ≤ (rankSymmetric128RootAllowance 13)^2) ∧
    (((4*rankSymmetric128Parameter 13-2)*(13 : ℝ)^2+(8*rankSymmetric128Parameter 13-5)*13-2) * rankSymmetric128IntegralWeight (13-1) +
      2 * rankSymmetric128RootAllowance 13 * (13 : ℝ) ≤ rankSymmetric128Coercivity 13 * (13 : ℝ)^2 * rankSymmetric128IntegralWeight 13) ∧
    (3 ≤ 13 → ((2*(13 : ℝ)^2+3*13-2) * rankSymmetric128IntegralWeight (13-1) +
      2 * rankSymmetric128RootAllowance 13 * (13 : ℝ) ≤ (13 : ℝ)^2 * rankSymmetric128CumulantWeight 13)) := by
  norm_num [rankSymmetric128Coercivity, rankSymmetric128Convolution, rankSymmetric128CauchyWeight, Finset.sum_Icc_succ_top]

theorem rankSymmetric128Certificate_14 :
    (rankSymmetric128IntegralWeight (14-1) * rankSymmetric128Convolution 14 ≤ (rankSymmetric128RootAllowance 14)^2) ∧
    (((4*rankSymmetric128Parameter 14-2)*(14 : ℝ)^2+(8*rankSymmetric128Parameter 14-5)*14-2) * rankSymmetric128IntegralWeight (14-1) +
      2 * rankSymmetric128RootAllowance 14 * (14 : ℝ) ≤ rankSymmetric128Coercivity 14 * (14 : ℝ)^2 * rankSymmetric128IntegralWeight 14) ∧
    (3 ≤ 14 → ((2*(14 : ℝ)^2+3*14-2) * rankSymmetric128IntegralWeight (14-1) +
      2 * rankSymmetric128RootAllowance 14 * (14 : ℝ) ≤ (14 : ℝ)^2 * rankSymmetric128CumulantWeight 14)) := by
  norm_num [rankSymmetric128Coercivity, rankSymmetric128Convolution, rankSymmetric128CauchyWeight, Finset.sum_Icc_succ_top]

theorem rankSymmetric128Certificate_15 :
    (rankSymmetric128IntegralWeight (15-1) * rankSymmetric128Convolution 15 ≤ (rankSymmetric128RootAllowance 15)^2) ∧
    (((4*rankSymmetric128Parameter 15-2)*(15 : ℝ)^2+(8*rankSymmetric128Parameter 15-5)*15-2) * rankSymmetric128IntegralWeight (15-1) +
      2 * rankSymmetric128RootAllowance 15 * (15 : ℝ) ≤ rankSymmetric128Coercivity 15 * (15 : ℝ)^2 * rankSymmetric128IntegralWeight 15) ∧
    (3 ≤ 15 → ((2*(15 : ℝ)^2+3*15-2) * rankSymmetric128IntegralWeight (15-1) +
      2 * rankSymmetric128RootAllowance 15 * (15 : ℝ) ≤ (15 : ℝ)^2 * rankSymmetric128CumulantWeight 15)) := by
  norm_num [rankSymmetric128Coercivity, rankSymmetric128Convolution, rankSymmetric128CauchyWeight, Finset.sum_Icc_succ_top]

theorem rankSymmetric128Certificate_16 :
    (rankSymmetric128IntegralWeight (16-1) * rankSymmetric128Convolution 16 ≤ (rankSymmetric128RootAllowance 16)^2) ∧
    (((4*rankSymmetric128Parameter 16-2)*(16 : ℝ)^2+(8*rankSymmetric128Parameter 16-5)*16-2) * rankSymmetric128IntegralWeight (16-1) +
      2 * rankSymmetric128RootAllowance 16 * (16 : ℝ) ≤ rankSymmetric128Coercivity 16 * (16 : ℝ)^2 * rankSymmetric128IntegralWeight 16) ∧
    (3 ≤ 16 → ((2*(16 : ℝ)^2+3*16-2) * rankSymmetric128IntegralWeight (16-1) +
      2 * rankSymmetric128RootAllowance 16 * (16 : ℝ) ≤ (16 : ℝ)^2 * rankSymmetric128CumulantWeight 16)) := by
  norm_num [rankSymmetric128Coercivity, rankSymmetric128Convolution, rankSymmetric128CauchyWeight, Finset.sum_Icc_succ_top]

theorem rankSymmetric128Certificate_17 :
    (rankSymmetric128IntegralWeight (17-1) * rankSymmetric128Convolution 17 ≤ (rankSymmetric128RootAllowance 17)^2) ∧
    (((4*rankSymmetric128Parameter 17-2)*(17 : ℝ)^2+(8*rankSymmetric128Parameter 17-5)*17-2) * rankSymmetric128IntegralWeight (17-1) +
      2 * rankSymmetric128RootAllowance 17 * (17 : ℝ) ≤ rankSymmetric128Coercivity 17 * (17 : ℝ)^2 * rankSymmetric128IntegralWeight 17) ∧
    (3 ≤ 17 → ((2*(17 : ℝ)^2+3*17-2) * rankSymmetric128IntegralWeight (17-1) +
      2 * rankSymmetric128RootAllowance 17 * (17 : ℝ) ≤ (17 : ℝ)^2 * rankSymmetric128CumulantWeight 17)) := by
  norm_num [rankSymmetric128Coercivity, rankSymmetric128Convolution, rankSymmetric128CauchyWeight, Finset.sum_Icc_succ_top]

end KLS.RouteArithmetic
end

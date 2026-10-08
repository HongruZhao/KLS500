import OptRankSymmetric128Weights

set_option maxRecDepth 8192

set_option maxHeartbeats 16000000
noncomputable section
namespace KLS.RouteArithmetic

theorem rankSymmetric128Certificate_18 :
    (rankSymmetric128IntegralWeight (18-1) * rankSymmetric128Convolution 18 ≤ (rankSymmetric128RootAllowance 18)^2) ∧
    (((4*rankSymmetric128Parameter 18-2)*(18 : ℝ)^2+(8*rankSymmetric128Parameter 18-5)*18-2) * rankSymmetric128IntegralWeight (18-1) +
      2 * rankSymmetric128RootAllowance 18 * (18 : ℝ) ≤ rankSymmetric128Coercivity 18 * (18 : ℝ)^2 * rankSymmetric128IntegralWeight 18) ∧
    (3 ≤ 18 → ((2*(18 : ℝ)^2+3*18-2) * rankSymmetric128IntegralWeight (18-1) +
      2 * rankSymmetric128RootAllowance 18 * (18 : ℝ) ≤ (18 : ℝ)^2 * rankSymmetric128CumulantWeight 18)) := by
  norm_num [rankSymmetric128Coercivity, rankSymmetric128Convolution, rankSymmetric128CauchyWeight, Finset.sum_Icc_succ_top]

theorem rankSymmetric128Certificate_19 :
    (rankSymmetric128IntegralWeight (19-1) * rankSymmetric128Convolution 19 ≤ (rankSymmetric128RootAllowance 19)^2) ∧
    (((4*rankSymmetric128Parameter 19-2)*(19 : ℝ)^2+(8*rankSymmetric128Parameter 19-5)*19-2) * rankSymmetric128IntegralWeight (19-1) +
      2 * rankSymmetric128RootAllowance 19 * (19 : ℝ) ≤ rankSymmetric128Coercivity 19 * (19 : ℝ)^2 * rankSymmetric128IntegralWeight 19) ∧
    (3 ≤ 19 → ((2*(19 : ℝ)^2+3*19-2) * rankSymmetric128IntegralWeight (19-1) +
      2 * rankSymmetric128RootAllowance 19 * (19 : ℝ) ≤ (19 : ℝ)^2 * rankSymmetric128CumulantWeight 19)) := by
  norm_num [rankSymmetric128Coercivity, rankSymmetric128Convolution, rankSymmetric128CauchyWeight, Finset.sum_Icc_succ_top]

theorem rankSymmetric128Certificate_20 :
    (rankSymmetric128IntegralWeight (20-1) * rankSymmetric128Convolution 20 ≤ (rankSymmetric128RootAllowance 20)^2) ∧
    (((4*rankSymmetric128Parameter 20-2)*(20 : ℝ)^2+(8*rankSymmetric128Parameter 20-5)*20-2) * rankSymmetric128IntegralWeight (20-1) +
      2 * rankSymmetric128RootAllowance 20 * (20 : ℝ) ≤ rankSymmetric128Coercivity 20 * (20 : ℝ)^2 * rankSymmetric128IntegralWeight 20) ∧
    (3 ≤ 20 → ((2*(20 : ℝ)^2+3*20-2) * rankSymmetric128IntegralWeight (20-1) +
      2 * rankSymmetric128RootAllowance 20 * (20 : ℝ) ≤ (20 : ℝ)^2 * rankSymmetric128CumulantWeight 20)) := by
  norm_num [rankSymmetric128Coercivity, rankSymmetric128Convolution, rankSymmetric128CauchyWeight, Finset.sum_Icc_succ_top]

theorem rankSymmetric128Certificate_21 :
    (rankSymmetric128IntegralWeight (21-1) * rankSymmetric128Convolution 21 ≤ (rankSymmetric128RootAllowance 21)^2) ∧
    (((4*rankSymmetric128Parameter 21-2)*(21 : ℝ)^2+(8*rankSymmetric128Parameter 21-5)*21-2) * rankSymmetric128IntegralWeight (21-1) +
      2 * rankSymmetric128RootAllowance 21 * (21 : ℝ) ≤ rankSymmetric128Coercivity 21 * (21 : ℝ)^2 * rankSymmetric128IntegralWeight 21) ∧
    (3 ≤ 21 → ((2*(21 : ℝ)^2+3*21-2) * rankSymmetric128IntegralWeight (21-1) +
      2 * rankSymmetric128RootAllowance 21 * (21 : ℝ) ≤ (21 : ℝ)^2 * rankSymmetric128CumulantWeight 21)) := by
  norm_num [rankSymmetric128Coercivity, rankSymmetric128Convolution, rankSymmetric128CauchyWeight, Finset.sum_Icc_succ_top]

theorem rankSymmetric128Certificate_22 :
    (rankSymmetric128IntegralWeight (22-1) * rankSymmetric128Convolution 22 ≤ (rankSymmetric128RootAllowance 22)^2) ∧
    (((4*rankSymmetric128Parameter 22-2)*(22 : ℝ)^2+(8*rankSymmetric128Parameter 22-5)*22-2) * rankSymmetric128IntegralWeight (22-1) +
      2 * rankSymmetric128RootAllowance 22 * (22 : ℝ) ≤ rankSymmetric128Coercivity 22 * (22 : ℝ)^2 * rankSymmetric128IntegralWeight 22) ∧
    (3 ≤ 22 → ((2*(22 : ℝ)^2+3*22-2) * rankSymmetric128IntegralWeight (22-1) +
      2 * rankSymmetric128RootAllowance 22 * (22 : ℝ) ≤ (22 : ℝ)^2 * rankSymmetric128CumulantWeight 22)) := by
  norm_num [rankSymmetric128Coercivity, rankSymmetric128Convolution, rankSymmetric128CauchyWeight, Finset.sum_Icc_succ_top]

theorem rankSymmetric128Certificate_23 :
    (rankSymmetric128IntegralWeight (23-1) * rankSymmetric128Convolution 23 ≤ (rankSymmetric128RootAllowance 23)^2) ∧
    (((4*rankSymmetric128Parameter 23-2)*(23 : ℝ)^2+(8*rankSymmetric128Parameter 23-5)*23-2) * rankSymmetric128IntegralWeight (23-1) +
      2 * rankSymmetric128RootAllowance 23 * (23 : ℝ) ≤ rankSymmetric128Coercivity 23 * (23 : ℝ)^2 * rankSymmetric128IntegralWeight 23) ∧
    (3 ≤ 23 → ((2*(23 : ℝ)^2+3*23-2) * rankSymmetric128IntegralWeight (23-1) +
      2 * rankSymmetric128RootAllowance 23 * (23 : ℝ) ≤ (23 : ℝ)^2 * rankSymmetric128CumulantWeight 23)) := by
  norm_num [rankSymmetric128Coercivity, rankSymmetric128Convolution, rankSymmetric128CauchyWeight, Finset.sum_Icc_succ_top]

theorem rankSymmetric128Certificate_24 :
    (rankSymmetric128IntegralWeight (24-1) * rankSymmetric128Convolution 24 ≤ (rankSymmetric128RootAllowance 24)^2) ∧
    (((4*rankSymmetric128Parameter 24-2)*(24 : ℝ)^2+(8*rankSymmetric128Parameter 24-5)*24-2) * rankSymmetric128IntegralWeight (24-1) +
      2 * rankSymmetric128RootAllowance 24 * (24 : ℝ) ≤ rankSymmetric128Coercivity 24 * (24 : ℝ)^2 * rankSymmetric128IntegralWeight 24) ∧
    (3 ≤ 24 → ((2*(24 : ℝ)^2+3*24-2) * rankSymmetric128IntegralWeight (24-1) +
      2 * rankSymmetric128RootAllowance 24 * (24 : ℝ) ≤ (24 : ℝ)^2 * rankSymmetric128CumulantWeight 24)) := by
  norm_num [rankSymmetric128Coercivity, rankSymmetric128Convolution, rankSymmetric128CauchyWeight, Finset.sum_Icc_succ_top]

theorem rankSymmetric128Certificate_25 :
    (rankSymmetric128IntegralWeight (25-1) * rankSymmetric128Convolution 25 ≤ (rankSymmetric128RootAllowance 25)^2) ∧
    (((4*rankSymmetric128Parameter 25-2)*(25 : ℝ)^2+(8*rankSymmetric128Parameter 25-5)*25-2) * rankSymmetric128IntegralWeight (25-1) +
      2 * rankSymmetric128RootAllowance 25 * (25 : ℝ) ≤ rankSymmetric128Coercivity 25 * (25 : ℝ)^2 * rankSymmetric128IntegralWeight 25) ∧
    (3 ≤ 25 → ((2*(25 : ℝ)^2+3*25-2) * rankSymmetric128IntegralWeight (25-1) +
      2 * rankSymmetric128RootAllowance 25 * (25 : ℝ) ≤ (25 : ℝ)^2 * rankSymmetric128CumulantWeight 25)) := by
  norm_num [rankSymmetric128Coercivity, rankSymmetric128Convolution, rankSymmetric128CauchyWeight, Finset.sum_Icc_succ_top]

end KLS.RouteArithmetic
end

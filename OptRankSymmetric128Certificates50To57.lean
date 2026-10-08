import OptRankSymmetric128Weights

set_option maxRecDepth 8192

set_option maxHeartbeats 16000000
noncomputable section
namespace KLS.RouteArithmetic

theorem rankSymmetric128Certificate_50 :
    (rankSymmetric128IntegralWeight (50-1) * rankSymmetric128Convolution 50 ≤ (rankSymmetric128RootAllowance 50)^2) ∧
    (((4*rankSymmetric128Parameter 50-2)*(50 : ℝ)^2+(8*rankSymmetric128Parameter 50-5)*50-2) * rankSymmetric128IntegralWeight (50-1) +
      2 * rankSymmetric128RootAllowance 50 * (50 : ℝ) ≤ rankSymmetric128Coercivity 50 * (50 : ℝ)^2 * rankSymmetric128IntegralWeight 50) ∧
    (3 ≤ 50 → ((2*(50 : ℝ)^2+3*50-2) * rankSymmetric128IntegralWeight (50-1) +
      2 * rankSymmetric128RootAllowance 50 * (50 : ℝ) ≤ (50 : ℝ)^2 * rankSymmetric128CumulantWeight 50)) := by
  norm_num [rankSymmetric128Coercivity, rankSymmetric128Convolution, rankSymmetric128CauchyWeight, Finset.sum_Icc_succ_top]

theorem rankSymmetric128Certificate_51 :
    (rankSymmetric128IntegralWeight (51-1) * rankSymmetric128Convolution 51 ≤ (rankSymmetric128RootAllowance 51)^2) ∧
    (((4*rankSymmetric128Parameter 51-2)*(51 : ℝ)^2+(8*rankSymmetric128Parameter 51-5)*51-2) * rankSymmetric128IntegralWeight (51-1) +
      2 * rankSymmetric128RootAllowance 51 * (51 : ℝ) ≤ rankSymmetric128Coercivity 51 * (51 : ℝ)^2 * rankSymmetric128IntegralWeight 51) ∧
    (3 ≤ 51 → ((2*(51 : ℝ)^2+3*51-2) * rankSymmetric128IntegralWeight (51-1) +
      2 * rankSymmetric128RootAllowance 51 * (51 : ℝ) ≤ (51 : ℝ)^2 * rankSymmetric128CumulantWeight 51)) := by
  norm_num [rankSymmetric128Coercivity, rankSymmetric128Convolution, rankSymmetric128CauchyWeight, Finset.sum_Icc_succ_top]

theorem rankSymmetric128Certificate_52 :
    (rankSymmetric128IntegralWeight (52-1) * rankSymmetric128Convolution 52 ≤ (rankSymmetric128RootAllowance 52)^2) ∧
    (((4*rankSymmetric128Parameter 52-2)*(52 : ℝ)^2+(8*rankSymmetric128Parameter 52-5)*52-2) * rankSymmetric128IntegralWeight (52-1) +
      2 * rankSymmetric128RootAllowance 52 * (52 : ℝ) ≤ rankSymmetric128Coercivity 52 * (52 : ℝ)^2 * rankSymmetric128IntegralWeight 52) ∧
    (3 ≤ 52 → ((2*(52 : ℝ)^2+3*52-2) * rankSymmetric128IntegralWeight (52-1) +
      2 * rankSymmetric128RootAllowance 52 * (52 : ℝ) ≤ (52 : ℝ)^2 * rankSymmetric128CumulantWeight 52)) := by
  norm_num [rankSymmetric128Coercivity, rankSymmetric128Convolution, rankSymmetric128CauchyWeight, Finset.sum_Icc_succ_top]

theorem rankSymmetric128Certificate_53 :
    (rankSymmetric128IntegralWeight (53-1) * rankSymmetric128Convolution 53 ≤ (rankSymmetric128RootAllowance 53)^2) ∧
    (((4*rankSymmetric128Parameter 53-2)*(53 : ℝ)^2+(8*rankSymmetric128Parameter 53-5)*53-2) * rankSymmetric128IntegralWeight (53-1) +
      2 * rankSymmetric128RootAllowance 53 * (53 : ℝ) ≤ rankSymmetric128Coercivity 53 * (53 : ℝ)^2 * rankSymmetric128IntegralWeight 53) ∧
    (3 ≤ 53 → ((2*(53 : ℝ)^2+3*53-2) * rankSymmetric128IntegralWeight (53-1) +
      2 * rankSymmetric128RootAllowance 53 * (53 : ℝ) ≤ (53 : ℝ)^2 * rankSymmetric128CumulantWeight 53)) := by
  norm_num [rankSymmetric128Coercivity, rankSymmetric128Convolution, rankSymmetric128CauchyWeight, Finset.sum_Icc_succ_top]

theorem rankSymmetric128Certificate_54 :
    (rankSymmetric128IntegralWeight (54-1) * rankSymmetric128Convolution 54 ≤ (rankSymmetric128RootAllowance 54)^2) ∧
    (((4*rankSymmetric128Parameter 54-2)*(54 : ℝ)^2+(8*rankSymmetric128Parameter 54-5)*54-2) * rankSymmetric128IntegralWeight (54-1) +
      2 * rankSymmetric128RootAllowance 54 * (54 : ℝ) ≤ rankSymmetric128Coercivity 54 * (54 : ℝ)^2 * rankSymmetric128IntegralWeight 54) ∧
    (3 ≤ 54 → ((2*(54 : ℝ)^2+3*54-2) * rankSymmetric128IntegralWeight (54-1) +
      2 * rankSymmetric128RootAllowance 54 * (54 : ℝ) ≤ (54 : ℝ)^2 * rankSymmetric128CumulantWeight 54)) := by
  norm_num [rankSymmetric128Coercivity, rankSymmetric128Convolution, rankSymmetric128CauchyWeight, Finset.sum_Icc_succ_top]

theorem rankSymmetric128Certificate_55 :
    (rankSymmetric128IntegralWeight (55-1) * rankSymmetric128Convolution 55 ≤ (rankSymmetric128RootAllowance 55)^2) ∧
    (((4*rankSymmetric128Parameter 55-2)*(55 : ℝ)^2+(8*rankSymmetric128Parameter 55-5)*55-2) * rankSymmetric128IntegralWeight (55-1) +
      2 * rankSymmetric128RootAllowance 55 * (55 : ℝ) ≤ rankSymmetric128Coercivity 55 * (55 : ℝ)^2 * rankSymmetric128IntegralWeight 55) ∧
    (3 ≤ 55 → ((2*(55 : ℝ)^2+3*55-2) * rankSymmetric128IntegralWeight (55-1) +
      2 * rankSymmetric128RootAllowance 55 * (55 : ℝ) ≤ (55 : ℝ)^2 * rankSymmetric128CumulantWeight 55)) := by
  norm_num [rankSymmetric128Coercivity, rankSymmetric128Convolution, rankSymmetric128CauchyWeight, Finset.sum_Icc_succ_top]

theorem rankSymmetric128Certificate_56 :
    (rankSymmetric128IntegralWeight (56-1) * rankSymmetric128Convolution 56 ≤ (rankSymmetric128RootAllowance 56)^2) ∧
    (((4*rankSymmetric128Parameter 56-2)*(56 : ℝ)^2+(8*rankSymmetric128Parameter 56-5)*56-2) * rankSymmetric128IntegralWeight (56-1) +
      2 * rankSymmetric128RootAllowance 56 * (56 : ℝ) ≤ rankSymmetric128Coercivity 56 * (56 : ℝ)^2 * rankSymmetric128IntegralWeight 56) ∧
    (3 ≤ 56 → ((2*(56 : ℝ)^2+3*56-2) * rankSymmetric128IntegralWeight (56-1) +
      2 * rankSymmetric128RootAllowance 56 * (56 : ℝ) ≤ (56 : ℝ)^2 * rankSymmetric128CumulantWeight 56)) := by
  norm_num [rankSymmetric128Coercivity, rankSymmetric128Convolution, rankSymmetric128CauchyWeight, Finset.sum_Icc_succ_top]

theorem rankSymmetric128Certificate_57 :
    (rankSymmetric128IntegralWeight (57-1) * rankSymmetric128Convolution 57 ≤ (rankSymmetric128RootAllowance 57)^2) ∧
    (((4*rankSymmetric128Parameter 57-2)*(57 : ℝ)^2+(8*rankSymmetric128Parameter 57-5)*57-2) * rankSymmetric128IntegralWeight (57-1) +
      2 * rankSymmetric128RootAllowance 57 * (57 : ℝ) ≤ rankSymmetric128Coercivity 57 * (57 : ℝ)^2 * rankSymmetric128IntegralWeight 57) ∧
    (3 ≤ 57 → ((2*(57 : ℝ)^2+3*57-2) * rankSymmetric128IntegralWeight (57-1) +
      2 * rankSymmetric128RootAllowance 57 * (57 : ℝ) ≤ (57 : ℝ)^2 * rankSymmetric128CumulantWeight 57)) := by
  norm_num [rankSymmetric128Coercivity, rankSymmetric128Convolution, rankSymmetric128CauchyWeight, Finset.sum_Icc_succ_top]

end KLS.RouteArithmetic
end

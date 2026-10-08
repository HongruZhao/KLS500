import OptRankSymmetric128Weights

set_option maxRecDepth 8192

set_option maxHeartbeats 16000000
noncomputable section
namespace KLS.RouteArithmetic

theorem rankSymmetric128Certificate_26 :
    (rankSymmetric128IntegralWeight (26-1) * rankSymmetric128Convolution 26 ≤ (rankSymmetric128RootAllowance 26)^2) ∧
    (((4*rankSymmetric128Parameter 26-2)*(26 : ℝ)^2+(8*rankSymmetric128Parameter 26-5)*26-2) * rankSymmetric128IntegralWeight (26-1) +
      2 * rankSymmetric128RootAllowance 26 * (26 : ℝ) ≤ rankSymmetric128Coercivity 26 * (26 : ℝ)^2 * rankSymmetric128IntegralWeight 26) ∧
    (3 ≤ 26 → ((2*(26 : ℝ)^2+3*26-2) * rankSymmetric128IntegralWeight (26-1) +
      2 * rankSymmetric128RootAllowance 26 * (26 : ℝ) ≤ (26 : ℝ)^2 * rankSymmetric128CumulantWeight 26)) := by
  norm_num [rankSymmetric128Coercivity, rankSymmetric128Convolution, rankSymmetric128CauchyWeight, Finset.sum_Icc_succ_top]

theorem rankSymmetric128Certificate_27 :
    (rankSymmetric128IntegralWeight (27-1) * rankSymmetric128Convolution 27 ≤ (rankSymmetric128RootAllowance 27)^2) ∧
    (((4*rankSymmetric128Parameter 27-2)*(27 : ℝ)^2+(8*rankSymmetric128Parameter 27-5)*27-2) * rankSymmetric128IntegralWeight (27-1) +
      2 * rankSymmetric128RootAllowance 27 * (27 : ℝ) ≤ rankSymmetric128Coercivity 27 * (27 : ℝ)^2 * rankSymmetric128IntegralWeight 27) ∧
    (3 ≤ 27 → ((2*(27 : ℝ)^2+3*27-2) * rankSymmetric128IntegralWeight (27-1) +
      2 * rankSymmetric128RootAllowance 27 * (27 : ℝ) ≤ (27 : ℝ)^2 * rankSymmetric128CumulantWeight 27)) := by
  norm_num [rankSymmetric128Coercivity, rankSymmetric128Convolution, rankSymmetric128CauchyWeight, Finset.sum_Icc_succ_top]

theorem rankSymmetric128Certificate_28 :
    (rankSymmetric128IntegralWeight (28-1) * rankSymmetric128Convolution 28 ≤ (rankSymmetric128RootAllowance 28)^2) ∧
    (((4*rankSymmetric128Parameter 28-2)*(28 : ℝ)^2+(8*rankSymmetric128Parameter 28-5)*28-2) * rankSymmetric128IntegralWeight (28-1) +
      2 * rankSymmetric128RootAllowance 28 * (28 : ℝ) ≤ rankSymmetric128Coercivity 28 * (28 : ℝ)^2 * rankSymmetric128IntegralWeight 28) ∧
    (3 ≤ 28 → ((2*(28 : ℝ)^2+3*28-2) * rankSymmetric128IntegralWeight (28-1) +
      2 * rankSymmetric128RootAllowance 28 * (28 : ℝ) ≤ (28 : ℝ)^2 * rankSymmetric128CumulantWeight 28)) := by
  norm_num [rankSymmetric128Coercivity, rankSymmetric128Convolution, rankSymmetric128CauchyWeight, Finset.sum_Icc_succ_top]

theorem rankSymmetric128Certificate_29 :
    (rankSymmetric128IntegralWeight (29-1) * rankSymmetric128Convolution 29 ≤ (rankSymmetric128RootAllowance 29)^2) ∧
    (((4*rankSymmetric128Parameter 29-2)*(29 : ℝ)^2+(8*rankSymmetric128Parameter 29-5)*29-2) * rankSymmetric128IntegralWeight (29-1) +
      2 * rankSymmetric128RootAllowance 29 * (29 : ℝ) ≤ rankSymmetric128Coercivity 29 * (29 : ℝ)^2 * rankSymmetric128IntegralWeight 29) ∧
    (3 ≤ 29 → ((2*(29 : ℝ)^2+3*29-2) * rankSymmetric128IntegralWeight (29-1) +
      2 * rankSymmetric128RootAllowance 29 * (29 : ℝ) ≤ (29 : ℝ)^2 * rankSymmetric128CumulantWeight 29)) := by
  norm_num [rankSymmetric128Coercivity, rankSymmetric128Convolution, rankSymmetric128CauchyWeight, Finset.sum_Icc_succ_top]

theorem rankSymmetric128Certificate_30 :
    (rankSymmetric128IntegralWeight (30-1) * rankSymmetric128Convolution 30 ≤ (rankSymmetric128RootAllowance 30)^2) ∧
    (((4*rankSymmetric128Parameter 30-2)*(30 : ℝ)^2+(8*rankSymmetric128Parameter 30-5)*30-2) * rankSymmetric128IntegralWeight (30-1) +
      2 * rankSymmetric128RootAllowance 30 * (30 : ℝ) ≤ rankSymmetric128Coercivity 30 * (30 : ℝ)^2 * rankSymmetric128IntegralWeight 30) ∧
    (3 ≤ 30 → ((2*(30 : ℝ)^2+3*30-2) * rankSymmetric128IntegralWeight (30-1) +
      2 * rankSymmetric128RootAllowance 30 * (30 : ℝ) ≤ (30 : ℝ)^2 * rankSymmetric128CumulantWeight 30)) := by
  norm_num [rankSymmetric128Coercivity, rankSymmetric128Convolution, rankSymmetric128CauchyWeight, Finset.sum_Icc_succ_top]

theorem rankSymmetric128Certificate_31 :
    (rankSymmetric128IntegralWeight (31-1) * rankSymmetric128Convolution 31 ≤ (rankSymmetric128RootAllowance 31)^2) ∧
    (((4*rankSymmetric128Parameter 31-2)*(31 : ℝ)^2+(8*rankSymmetric128Parameter 31-5)*31-2) * rankSymmetric128IntegralWeight (31-1) +
      2 * rankSymmetric128RootAllowance 31 * (31 : ℝ) ≤ rankSymmetric128Coercivity 31 * (31 : ℝ)^2 * rankSymmetric128IntegralWeight 31) ∧
    (3 ≤ 31 → ((2*(31 : ℝ)^2+3*31-2) * rankSymmetric128IntegralWeight (31-1) +
      2 * rankSymmetric128RootAllowance 31 * (31 : ℝ) ≤ (31 : ℝ)^2 * rankSymmetric128CumulantWeight 31)) := by
  norm_num [rankSymmetric128Coercivity, rankSymmetric128Convolution, rankSymmetric128CauchyWeight, Finset.sum_Icc_succ_top]

theorem rankSymmetric128Certificate_32 :
    (rankSymmetric128IntegralWeight (32-1) * rankSymmetric128Convolution 32 ≤ (rankSymmetric128RootAllowance 32)^2) ∧
    (((4*rankSymmetric128Parameter 32-2)*(32 : ℝ)^2+(8*rankSymmetric128Parameter 32-5)*32-2) * rankSymmetric128IntegralWeight (32-1) +
      2 * rankSymmetric128RootAllowance 32 * (32 : ℝ) ≤ rankSymmetric128Coercivity 32 * (32 : ℝ)^2 * rankSymmetric128IntegralWeight 32) ∧
    (3 ≤ 32 → ((2*(32 : ℝ)^2+3*32-2) * rankSymmetric128IntegralWeight (32-1) +
      2 * rankSymmetric128RootAllowance 32 * (32 : ℝ) ≤ (32 : ℝ)^2 * rankSymmetric128CumulantWeight 32)) := by
  norm_num [rankSymmetric128Coercivity, rankSymmetric128Convolution, rankSymmetric128CauchyWeight, Finset.sum_Icc_succ_top]

theorem rankSymmetric128Certificate_33 :
    (rankSymmetric128IntegralWeight (33-1) * rankSymmetric128Convolution 33 ≤ (rankSymmetric128RootAllowance 33)^2) ∧
    (((4*rankSymmetric128Parameter 33-2)*(33 : ℝ)^2+(8*rankSymmetric128Parameter 33-5)*33-2) * rankSymmetric128IntegralWeight (33-1) +
      2 * rankSymmetric128RootAllowance 33 * (33 : ℝ) ≤ rankSymmetric128Coercivity 33 * (33 : ℝ)^2 * rankSymmetric128IntegralWeight 33) ∧
    (3 ≤ 33 → ((2*(33 : ℝ)^2+3*33-2) * rankSymmetric128IntegralWeight (33-1) +
      2 * rankSymmetric128RootAllowance 33 * (33 : ℝ) ≤ (33 : ℝ)^2 * rankSymmetric128CumulantWeight 33)) := by
  norm_num [rankSymmetric128Coercivity, rankSymmetric128Convolution, rankSymmetric128CauchyWeight, Finset.sum_Icc_succ_top]

end KLS.RouteArithmetic
end

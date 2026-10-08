import OptRankSymmetric256Weights

set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
noncomputable section
namespace KLS.RouteArithmetic

theorem rankSymmetric256Certificate_193 :
    (rankSymmetric256IntegralWeight (193-1) * rankSymmetric256Convolution 193 ≤ (rankSymmetric256RootAllowance 193)^2) ∧
    (((4*rankSymmetric256Parameter 193-2)*(193 : ℝ)^2+(8*rankSymmetric256Parameter 193-5)*193-2) * rankSymmetric256IntegralWeight (193-1) +
      2 * rankSymmetric256RootAllowance 193 * (193 : ℝ) ≤ rankSymmetric256Coercivity 193 * (193 : ℝ)^2 * rankSymmetric256IntegralWeight 193) ∧
    (((2*(193 : ℝ)^2+3*193-2) * rankSymmetric256IntegralWeight (193-1) +
      2 * rankSymmetric256RootAllowance 193 * (193 : ℝ) ≤ (193 : ℝ)^2 * rankSymmetric256CumulantWeight 193)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset193, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_194 :
    (rankSymmetric256IntegralWeight (194-1) * rankSymmetric256Convolution 194 ≤ (rankSymmetric256RootAllowance 194)^2) ∧
    (((4*rankSymmetric256Parameter 194-2)*(194 : ℝ)^2+(8*rankSymmetric256Parameter 194-5)*194-2) * rankSymmetric256IntegralWeight (194-1) +
      2 * rankSymmetric256RootAllowance 194 * (194 : ℝ) ≤ rankSymmetric256Coercivity 194 * (194 : ℝ)^2 * rankSymmetric256IntegralWeight 194) ∧
    (((2*(194 : ℝ)^2+3*194-2) * rankSymmetric256IntegralWeight (194-1) +
      2 * rankSymmetric256RootAllowance 194 * (194 : ℝ) ≤ (194 : ℝ)^2 * rankSymmetric256CumulantWeight 194)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset194, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_195 :
    (rankSymmetric256IntegralWeight (195-1) * rankSymmetric256Convolution 195 ≤ (rankSymmetric256RootAllowance 195)^2) ∧
    (((4*rankSymmetric256Parameter 195-2)*(195 : ℝ)^2+(8*rankSymmetric256Parameter 195-5)*195-2) * rankSymmetric256IntegralWeight (195-1) +
      2 * rankSymmetric256RootAllowance 195 * (195 : ℝ) ≤ rankSymmetric256Coercivity 195 * (195 : ℝ)^2 * rankSymmetric256IntegralWeight 195) ∧
    (((2*(195 : ℝ)^2+3*195-2) * rankSymmetric256IntegralWeight (195-1) +
      2 * rankSymmetric256RootAllowance 195 * (195 : ℝ) ≤ (195 : ℝ)^2 * rankSymmetric256CumulantWeight 195)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset195, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_196 :
    (rankSymmetric256IntegralWeight (196-1) * rankSymmetric256Convolution 196 ≤ (rankSymmetric256RootAllowance 196)^2) ∧
    (((4*rankSymmetric256Parameter 196-2)*(196 : ℝ)^2+(8*rankSymmetric256Parameter 196-5)*196-2) * rankSymmetric256IntegralWeight (196-1) +
      2 * rankSymmetric256RootAllowance 196 * (196 : ℝ) ≤ rankSymmetric256Coercivity 196 * (196 : ℝ)^2 * rankSymmetric256IntegralWeight 196) ∧
    (((2*(196 : ℝ)^2+3*196-2) * rankSymmetric256IntegralWeight (196-1) +
      2 * rankSymmetric256RootAllowance 196 * (196 : ℝ) ≤ (196 : ℝ)^2 * rankSymmetric256CumulantWeight 196)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset196, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_197 :
    (rankSymmetric256IntegralWeight (197-1) * rankSymmetric256Convolution 197 ≤ (rankSymmetric256RootAllowance 197)^2) ∧
    (((4*rankSymmetric256Parameter 197-2)*(197 : ℝ)^2+(8*rankSymmetric256Parameter 197-5)*197-2) * rankSymmetric256IntegralWeight (197-1) +
      2 * rankSymmetric256RootAllowance 197 * (197 : ℝ) ≤ rankSymmetric256Coercivity 197 * (197 : ℝ)^2 * rankSymmetric256IntegralWeight 197) ∧
    (((2*(197 : ℝ)^2+3*197-2) * rankSymmetric256IntegralWeight (197-1) +
      2 * rankSymmetric256RootAllowance 197 * (197 : ℝ) ≤ (197 : ℝ)^2 * rankSymmetric256CumulantWeight 197)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset197, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_198 :
    (rankSymmetric256IntegralWeight (198-1) * rankSymmetric256Convolution 198 ≤ (rankSymmetric256RootAllowance 198)^2) ∧
    (((4*rankSymmetric256Parameter 198-2)*(198 : ℝ)^2+(8*rankSymmetric256Parameter 198-5)*198-2) * rankSymmetric256IntegralWeight (198-1) +
      2 * rankSymmetric256RootAllowance 198 * (198 : ℝ) ≤ rankSymmetric256Coercivity 198 * (198 : ℝ)^2 * rankSymmetric256IntegralWeight 198) ∧
    (((2*(198 : ℝ)^2+3*198-2) * rankSymmetric256IntegralWeight (198-1) +
      2 * rankSymmetric256RootAllowance 198 * (198 : ℝ) ≤ (198 : ℝ)^2 * rankSymmetric256CumulantWeight 198)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset198, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_199 :
    (rankSymmetric256IntegralWeight (199-1) * rankSymmetric256Convolution 199 ≤ (rankSymmetric256RootAllowance 199)^2) ∧
    (((4*rankSymmetric256Parameter 199-2)*(199 : ℝ)^2+(8*rankSymmetric256Parameter 199-5)*199-2) * rankSymmetric256IntegralWeight (199-1) +
      2 * rankSymmetric256RootAllowance 199 * (199 : ℝ) ≤ rankSymmetric256Coercivity 199 * (199 : ℝ)^2 * rankSymmetric256IntegralWeight 199) ∧
    (((2*(199 : ℝ)^2+3*199-2) * rankSymmetric256IntegralWeight (199-1) +
      2 * rankSymmetric256RootAllowance 199 * (199 : ℝ) ≤ (199 : ℝ)^2 * rankSymmetric256CumulantWeight 199)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset199, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_200 :
    (rankSymmetric256IntegralWeight (200-1) * rankSymmetric256Convolution 200 ≤ (rankSymmetric256RootAllowance 200)^2) ∧
    (((4*rankSymmetric256Parameter 200-2)*(200 : ℝ)^2+(8*rankSymmetric256Parameter 200-5)*200-2) * rankSymmetric256IntegralWeight (200-1) +
      2 * rankSymmetric256RootAllowance 200 * (200 : ℝ) ≤ rankSymmetric256Coercivity 200 * (200 : ℝ)^2 * rankSymmetric256IntegralWeight 200) ∧
    (((2*(200 : ℝ)^2+3*200-2) * rankSymmetric256IntegralWeight (200-1) +
      2 * rankSymmetric256RootAllowance 200 * (200 : ℝ) ≤ (200 : ℝ)^2 * rankSymmetric256CumulantWeight 200)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset200, Finset.sum_Icc_succ_top]

end KLS.RouteArithmetic
end

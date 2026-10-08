import OptRankSymmetric256Weights

set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
noncomputable section
namespace KLS.RouteArithmetic

theorem rankSymmetric256Certificate_233 :
    (rankSymmetric256IntegralWeight (233-1) * rankSymmetric256Convolution 233 ≤ (rankSymmetric256RootAllowance 233)^2) ∧
    (((4*rankSymmetric256Parameter 233-2)*(233 : ℝ)^2+(8*rankSymmetric256Parameter 233-5)*233-2) * rankSymmetric256IntegralWeight (233-1) +
      2 * rankSymmetric256RootAllowance 233 * (233 : ℝ) ≤ rankSymmetric256Coercivity 233 * (233 : ℝ)^2 * rankSymmetric256IntegralWeight 233) ∧
    (((2*(233 : ℝ)^2+3*233-2) * rankSymmetric256IntegralWeight (233-1) +
      2 * rankSymmetric256RootAllowance 233 * (233 : ℝ) ≤ (233 : ℝ)^2 * rankSymmetric256CumulantWeight 233)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset233, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_234 :
    (rankSymmetric256IntegralWeight (234-1) * rankSymmetric256Convolution 234 ≤ (rankSymmetric256RootAllowance 234)^2) ∧
    (((4*rankSymmetric256Parameter 234-2)*(234 : ℝ)^2+(8*rankSymmetric256Parameter 234-5)*234-2) * rankSymmetric256IntegralWeight (234-1) +
      2 * rankSymmetric256RootAllowance 234 * (234 : ℝ) ≤ rankSymmetric256Coercivity 234 * (234 : ℝ)^2 * rankSymmetric256IntegralWeight 234) ∧
    (((2*(234 : ℝ)^2+3*234-2) * rankSymmetric256IntegralWeight (234-1) +
      2 * rankSymmetric256RootAllowance 234 * (234 : ℝ) ≤ (234 : ℝ)^2 * rankSymmetric256CumulantWeight 234)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset234, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_235 :
    (rankSymmetric256IntegralWeight (235-1) * rankSymmetric256Convolution 235 ≤ (rankSymmetric256RootAllowance 235)^2) ∧
    (((4*rankSymmetric256Parameter 235-2)*(235 : ℝ)^2+(8*rankSymmetric256Parameter 235-5)*235-2) * rankSymmetric256IntegralWeight (235-1) +
      2 * rankSymmetric256RootAllowance 235 * (235 : ℝ) ≤ rankSymmetric256Coercivity 235 * (235 : ℝ)^2 * rankSymmetric256IntegralWeight 235) ∧
    (((2*(235 : ℝ)^2+3*235-2) * rankSymmetric256IntegralWeight (235-1) +
      2 * rankSymmetric256RootAllowance 235 * (235 : ℝ) ≤ (235 : ℝ)^2 * rankSymmetric256CumulantWeight 235)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset235, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_236 :
    (rankSymmetric256IntegralWeight (236-1) * rankSymmetric256Convolution 236 ≤ (rankSymmetric256RootAllowance 236)^2) ∧
    (((4*rankSymmetric256Parameter 236-2)*(236 : ℝ)^2+(8*rankSymmetric256Parameter 236-5)*236-2) * rankSymmetric256IntegralWeight (236-1) +
      2 * rankSymmetric256RootAllowance 236 * (236 : ℝ) ≤ rankSymmetric256Coercivity 236 * (236 : ℝ)^2 * rankSymmetric256IntegralWeight 236) ∧
    (((2*(236 : ℝ)^2+3*236-2) * rankSymmetric256IntegralWeight (236-1) +
      2 * rankSymmetric256RootAllowance 236 * (236 : ℝ) ≤ (236 : ℝ)^2 * rankSymmetric256CumulantWeight 236)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset236, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_237 :
    (rankSymmetric256IntegralWeight (237-1) * rankSymmetric256Convolution 237 ≤ (rankSymmetric256RootAllowance 237)^2) ∧
    (((4*rankSymmetric256Parameter 237-2)*(237 : ℝ)^2+(8*rankSymmetric256Parameter 237-5)*237-2) * rankSymmetric256IntegralWeight (237-1) +
      2 * rankSymmetric256RootAllowance 237 * (237 : ℝ) ≤ rankSymmetric256Coercivity 237 * (237 : ℝ)^2 * rankSymmetric256IntegralWeight 237) ∧
    (((2*(237 : ℝ)^2+3*237-2) * rankSymmetric256IntegralWeight (237-1) +
      2 * rankSymmetric256RootAllowance 237 * (237 : ℝ) ≤ (237 : ℝ)^2 * rankSymmetric256CumulantWeight 237)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset237, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_238 :
    (rankSymmetric256IntegralWeight (238-1) * rankSymmetric256Convolution 238 ≤ (rankSymmetric256RootAllowance 238)^2) ∧
    (((4*rankSymmetric256Parameter 238-2)*(238 : ℝ)^2+(8*rankSymmetric256Parameter 238-5)*238-2) * rankSymmetric256IntegralWeight (238-1) +
      2 * rankSymmetric256RootAllowance 238 * (238 : ℝ) ≤ rankSymmetric256Coercivity 238 * (238 : ℝ)^2 * rankSymmetric256IntegralWeight 238) ∧
    (((2*(238 : ℝ)^2+3*238-2) * rankSymmetric256IntegralWeight (238-1) +
      2 * rankSymmetric256RootAllowance 238 * (238 : ℝ) ≤ (238 : ℝ)^2 * rankSymmetric256CumulantWeight 238)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset238, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_239 :
    (rankSymmetric256IntegralWeight (239-1) * rankSymmetric256Convolution 239 ≤ (rankSymmetric256RootAllowance 239)^2) ∧
    (((4*rankSymmetric256Parameter 239-2)*(239 : ℝ)^2+(8*rankSymmetric256Parameter 239-5)*239-2) * rankSymmetric256IntegralWeight (239-1) +
      2 * rankSymmetric256RootAllowance 239 * (239 : ℝ) ≤ rankSymmetric256Coercivity 239 * (239 : ℝ)^2 * rankSymmetric256IntegralWeight 239) ∧
    (((2*(239 : ℝ)^2+3*239-2) * rankSymmetric256IntegralWeight (239-1) +
      2 * rankSymmetric256RootAllowance 239 * (239 : ℝ) ≤ (239 : ℝ)^2 * rankSymmetric256CumulantWeight 239)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset239, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_240 :
    (rankSymmetric256IntegralWeight (240-1) * rankSymmetric256Convolution 240 ≤ (rankSymmetric256RootAllowance 240)^2) ∧
    (((4*rankSymmetric256Parameter 240-2)*(240 : ℝ)^2+(8*rankSymmetric256Parameter 240-5)*240-2) * rankSymmetric256IntegralWeight (240-1) +
      2 * rankSymmetric256RootAllowance 240 * (240 : ℝ) ≤ rankSymmetric256Coercivity 240 * (240 : ℝ)^2 * rankSymmetric256IntegralWeight 240) ∧
    (((2*(240 : ℝ)^2+3*240-2) * rankSymmetric256IntegralWeight (240-1) +
      2 * rankSymmetric256RootAllowance 240 * (240 : ℝ) ≤ (240 : ℝ)^2 * rankSymmetric256CumulantWeight 240)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset240, Finset.sum_Icc_succ_top]

end KLS.RouteArithmetic
end

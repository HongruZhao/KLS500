import OptRankSymmetric256Weights

set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
noncomputable section
namespace KLS.RouteArithmetic

theorem rankSymmetric256Certificate_241 :
    (rankSymmetric256IntegralWeight (241-1) * rankSymmetric256Convolution 241 ≤ (rankSymmetric256RootAllowance 241)^2) ∧
    (((4*rankSymmetric256Parameter 241-2)*(241 : ℝ)^2+(8*rankSymmetric256Parameter 241-5)*241-2) * rankSymmetric256IntegralWeight (241-1) +
      2 * rankSymmetric256RootAllowance 241 * (241 : ℝ) ≤ rankSymmetric256Coercivity 241 * (241 : ℝ)^2 * rankSymmetric256IntegralWeight 241) ∧
    (((2*(241 : ℝ)^2+3*241-2) * rankSymmetric256IntegralWeight (241-1) +
      2 * rankSymmetric256RootAllowance 241 * (241 : ℝ) ≤ (241 : ℝ)^2 * rankSymmetric256CumulantWeight 241)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset241, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_242 :
    (rankSymmetric256IntegralWeight (242-1) * rankSymmetric256Convolution 242 ≤ (rankSymmetric256RootAllowance 242)^2) ∧
    (((4*rankSymmetric256Parameter 242-2)*(242 : ℝ)^2+(8*rankSymmetric256Parameter 242-5)*242-2) * rankSymmetric256IntegralWeight (242-1) +
      2 * rankSymmetric256RootAllowance 242 * (242 : ℝ) ≤ rankSymmetric256Coercivity 242 * (242 : ℝ)^2 * rankSymmetric256IntegralWeight 242) ∧
    (((2*(242 : ℝ)^2+3*242-2) * rankSymmetric256IntegralWeight (242-1) +
      2 * rankSymmetric256RootAllowance 242 * (242 : ℝ) ≤ (242 : ℝ)^2 * rankSymmetric256CumulantWeight 242)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset242, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_243 :
    (rankSymmetric256IntegralWeight (243-1) * rankSymmetric256Convolution 243 ≤ (rankSymmetric256RootAllowance 243)^2) ∧
    (((4*rankSymmetric256Parameter 243-2)*(243 : ℝ)^2+(8*rankSymmetric256Parameter 243-5)*243-2) * rankSymmetric256IntegralWeight (243-1) +
      2 * rankSymmetric256RootAllowance 243 * (243 : ℝ) ≤ rankSymmetric256Coercivity 243 * (243 : ℝ)^2 * rankSymmetric256IntegralWeight 243) ∧
    (((2*(243 : ℝ)^2+3*243-2) * rankSymmetric256IntegralWeight (243-1) +
      2 * rankSymmetric256RootAllowance 243 * (243 : ℝ) ≤ (243 : ℝ)^2 * rankSymmetric256CumulantWeight 243)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset243, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_244 :
    (rankSymmetric256IntegralWeight (244-1) * rankSymmetric256Convolution 244 ≤ (rankSymmetric256RootAllowance 244)^2) ∧
    (((4*rankSymmetric256Parameter 244-2)*(244 : ℝ)^2+(8*rankSymmetric256Parameter 244-5)*244-2) * rankSymmetric256IntegralWeight (244-1) +
      2 * rankSymmetric256RootAllowance 244 * (244 : ℝ) ≤ rankSymmetric256Coercivity 244 * (244 : ℝ)^2 * rankSymmetric256IntegralWeight 244) ∧
    (((2*(244 : ℝ)^2+3*244-2) * rankSymmetric256IntegralWeight (244-1) +
      2 * rankSymmetric256RootAllowance 244 * (244 : ℝ) ≤ (244 : ℝ)^2 * rankSymmetric256CumulantWeight 244)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset244, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_245 :
    (rankSymmetric256IntegralWeight (245-1) * rankSymmetric256Convolution 245 ≤ (rankSymmetric256RootAllowance 245)^2) ∧
    (((4*rankSymmetric256Parameter 245-2)*(245 : ℝ)^2+(8*rankSymmetric256Parameter 245-5)*245-2) * rankSymmetric256IntegralWeight (245-1) +
      2 * rankSymmetric256RootAllowance 245 * (245 : ℝ) ≤ rankSymmetric256Coercivity 245 * (245 : ℝ)^2 * rankSymmetric256IntegralWeight 245) ∧
    (((2*(245 : ℝ)^2+3*245-2) * rankSymmetric256IntegralWeight (245-1) +
      2 * rankSymmetric256RootAllowance 245 * (245 : ℝ) ≤ (245 : ℝ)^2 * rankSymmetric256CumulantWeight 245)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset245, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_246 :
    (rankSymmetric256IntegralWeight (246-1) * rankSymmetric256Convolution 246 ≤ (rankSymmetric256RootAllowance 246)^2) ∧
    (((4*rankSymmetric256Parameter 246-2)*(246 : ℝ)^2+(8*rankSymmetric256Parameter 246-5)*246-2) * rankSymmetric256IntegralWeight (246-1) +
      2 * rankSymmetric256RootAllowance 246 * (246 : ℝ) ≤ rankSymmetric256Coercivity 246 * (246 : ℝ)^2 * rankSymmetric256IntegralWeight 246) ∧
    (((2*(246 : ℝ)^2+3*246-2) * rankSymmetric256IntegralWeight (246-1) +
      2 * rankSymmetric256RootAllowance 246 * (246 : ℝ) ≤ (246 : ℝ)^2 * rankSymmetric256CumulantWeight 246)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset246, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_247 :
    (rankSymmetric256IntegralWeight (247-1) * rankSymmetric256Convolution 247 ≤ (rankSymmetric256RootAllowance 247)^2) ∧
    (((4*rankSymmetric256Parameter 247-2)*(247 : ℝ)^2+(8*rankSymmetric256Parameter 247-5)*247-2) * rankSymmetric256IntegralWeight (247-1) +
      2 * rankSymmetric256RootAllowance 247 * (247 : ℝ) ≤ rankSymmetric256Coercivity 247 * (247 : ℝ)^2 * rankSymmetric256IntegralWeight 247) ∧
    (((2*(247 : ℝ)^2+3*247-2) * rankSymmetric256IntegralWeight (247-1) +
      2 * rankSymmetric256RootAllowance 247 * (247 : ℝ) ≤ (247 : ℝ)^2 * rankSymmetric256CumulantWeight 247)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset247, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_248 :
    (rankSymmetric256IntegralWeight (248-1) * rankSymmetric256Convolution 248 ≤ (rankSymmetric256RootAllowance 248)^2) ∧
    (((4*rankSymmetric256Parameter 248-2)*(248 : ℝ)^2+(8*rankSymmetric256Parameter 248-5)*248-2) * rankSymmetric256IntegralWeight (248-1) +
      2 * rankSymmetric256RootAllowance 248 * (248 : ℝ) ≤ rankSymmetric256Coercivity 248 * (248 : ℝ)^2 * rankSymmetric256IntegralWeight 248) ∧
    (((2*(248 : ℝ)^2+3*248-2) * rankSymmetric256IntegralWeight (248-1) +
      2 * rankSymmetric256RootAllowance 248 * (248 : ℝ) ≤ (248 : ℝ)^2 * rankSymmetric256CumulantWeight 248)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset248, Finset.sum_Icc_succ_top]

end KLS.RouteArithmetic
end

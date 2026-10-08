import OptRankSymmetric256Weights

set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
noncomputable section
namespace KLS.RouteArithmetic

theorem rankSymmetric256Certificate_225 :
    (rankSymmetric256IntegralWeight (225-1) * rankSymmetric256Convolution 225 ≤ (rankSymmetric256RootAllowance 225)^2) ∧
    (((4*rankSymmetric256Parameter 225-2)*(225 : ℝ)^2+(8*rankSymmetric256Parameter 225-5)*225-2) * rankSymmetric256IntegralWeight (225-1) +
      2 * rankSymmetric256RootAllowance 225 * (225 : ℝ) ≤ rankSymmetric256Coercivity 225 * (225 : ℝ)^2 * rankSymmetric256IntegralWeight 225) ∧
    (((2*(225 : ℝ)^2+3*225-2) * rankSymmetric256IntegralWeight (225-1) +
      2 * rankSymmetric256RootAllowance 225 * (225 : ℝ) ≤ (225 : ℝ)^2 * rankSymmetric256CumulantWeight 225)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset225, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_226 :
    (rankSymmetric256IntegralWeight (226-1) * rankSymmetric256Convolution 226 ≤ (rankSymmetric256RootAllowance 226)^2) ∧
    (((4*rankSymmetric256Parameter 226-2)*(226 : ℝ)^2+(8*rankSymmetric256Parameter 226-5)*226-2) * rankSymmetric256IntegralWeight (226-1) +
      2 * rankSymmetric256RootAllowance 226 * (226 : ℝ) ≤ rankSymmetric256Coercivity 226 * (226 : ℝ)^2 * rankSymmetric256IntegralWeight 226) ∧
    (((2*(226 : ℝ)^2+3*226-2) * rankSymmetric256IntegralWeight (226-1) +
      2 * rankSymmetric256RootAllowance 226 * (226 : ℝ) ≤ (226 : ℝ)^2 * rankSymmetric256CumulantWeight 226)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset226, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_227 :
    (rankSymmetric256IntegralWeight (227-1) * rankSymmetric256Convolution 227 ≤ (rankSymmetric256RootAllowance 227)^2) ∧
    (((4*rankSymmetric256Parameter 227-2)*(227 : ℝ)^2+(8*rankSymmetric256Parameter 227-5)*227-2) * rankSymmetric256IntegralWeight (227-1) +
      2 * rankSymmetric256RootAllowance 227 * (227 : ℝ) ≤ rankSymmetric256Coercivity 227 * (227 : ℝ)^2 * rankSymmetric256IntegralWeight 227) ∧
    (((2*(227 : ℝ)^2+3*227-2) * rankSymmetric256IntegralWeight (227-1) +
      2 * rankSymmetric256RootAllowance 227 * (227 : ℝ) ≤ (227 : ℝ)^2 * rankSymmetric256CumulantWeight 227)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset227, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_228 :
    (rankSymmetric256IntegralWeight (228-1) * rankSymmetric256Convolution 228 ≤ (rankSymmetric256RootAllowance 228)^2) ∧
    (((4*rankSymmetric256Parameter 228-2)*(228 : ℝ)^2+(8*rankSymmetric256Parameter 228-5)*228-2) * rankSymmetric256IntegralWeight (228-1) +
      2 * rankSymmetric256RootAllowance 228 * (228 : ℝ) ≤ rankSymmetric256Coercivity 228 * (228 : ℝ)^2 * rankSymmetric256IntegralWeight 228) ∧
    (((2*(228 : ℝ)^2+3*228-2) * rankSymmetric256IntegralWeight (228-1) +
      2 * rankSymmetric256RootAllowance 228 * (228 : ℝ) ≤ (228 : ℝ)^2 * rankSymmetric256CumulantWeight 228)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset228, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_229 :
    (rankSymmetric256IntegralWeight (229-1) * rankSymmetric256Convolution 229 ≤ (rankSymmetric256RootAllowance 229)^2) ∧
    (((4*rankSymmetric256Parameter 229-2)*(229 : ℝ)^2+(8*rankSymmetric256Parameter 229-5)*229-2) * rankSymmetric256IntegralWeight (229-1) +
      2 * rankSymmetric256RootAllowance 229 * (229 : ℝ) ≤ rankSymmetric256Coercivity 229 * (229 : ℝ)^2 * rankSymmetric256IntegralWeight 229) ∧
    (((2*(229 : ℝ)^2+3*229-2) * rankSymmetric256IntegralWeight (229-1) +
      2 * rankSymmetric256RootAllowance 229 * (229 : ℝ) ≤ (229 : ℝ)^2 * rankSymmetric256CumulantWeight 229)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset229, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_230 :
    (rankSymmetric256IntegralWeight (230-1) * rankSymmetric256Convolution 230 ≤ (rankSymmetric256RootAllowance 230)^2) ∧
    (((4*rankSymmetric256Parameter 230-2)*(230 : ℝ)^2+(8*rankSymmetric256Parameter 230-5)*230-2) * rankSymmetric256IntegralWeight (230-1) +
      2 * rankSymmetric256RootAllowance 230 * (230 : ℝ) ≤ rankSymmetric256Coercivity 230 * (230 : ℝ)^2 * rankSymmetric256IntegralWeight 230) ∧
    (((2*(230 : ℝ)^2+3*230-2) * rankSymmetric256IntegralWeight (230-1) +
      2 * rankSymmetric256RootAllowance 230 * (230 : ℝ) ≤ (230 : ℝ)^2 * rankSymmetric256CumulantWeight 230)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset230, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_231 :
    (rankSymmetric256IntegralWeight (231-1) * rankSymmetric256Convolution 231 ≤ (rankSymmetric256RootAllowance 231)^2) ∧
    (((4*rankSymmetric256Parameter 231-2)*(231 : ℝ)^2+(8*rankSymmetric256Parameter 231-5)*231-2) * rankSymmetric256IntegralWeight (231-1) +
      2 * rankSymmetric256RootAllowance 231 * (231 : ℝ) ≤ rankSymmetric256Coercivity 231 * (231 : ℝ)^2 * rankSymmetric256IntegralWeight 231) ∧
    (((2*(231 : ℝ)^2+3*231-2) * rankSymmetric256IntegralWeight (231-1) +
      2 * rankSymmetric256RootAllowance 231 * (231 : ℝ) ≤ (231 : ℝ)^2 * rankSymmetric256CumulantWeight 231)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset231, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_232 :
    (rankSymmetric256IntegralWeight (232-1) * rankSymmetric256Convolution 232 ≤ (rankSymmetric256RootAllowance 232)^2) ∧
    (((4*rankSymmetric256Parameter 232-2)*(232 : ℝ)^2+(8*rankSymmetric256Parameter 232-5)*232-2) * rankSymmetric256IntegralWeight (232-1) +
      2 * rankSymmetric256RootAllowance 232 * (232 : ℝ) ≤ rankSymmetric256Coercivity 232 * (232 : ℝ)^2 * rankSymmetric256IntegralWeight 232) ∧
    (((2*(232 : ℝ)^2+3*232-2) * rankSymmetric256IntegralWeight (232-1) +
      2 * rankSymmetric256RootAllowance 232 * (232 : ℝ) ≤ (232 : ℝ)^2 * rankSymmetric256CumulantWeight 232)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset232, Finset.sum_Icc_succ_top]

end KLS.RouteArithmetic
end

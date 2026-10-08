import OptRankSymmetric256Weights

set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
noncomputable section
namespace KLS.RouteArithmetic

theorem rankSymmetric256Certificate_249 :
    (rankSymmetric256IntegralWeight (249-1) * rankSymmetric256Convolution 249 ≤ (rankSymmetric256RootAllowance 249)^2) ∧
    (((4*rankSymmetric256Parameter 249-2)*(249 : ℝ)^2+(8*rankSymmetric256Parameter 249-5)*249-2) * rankSymmetric256IntegralWeight (249-1) +
      2 * rankSymmetric256RootAllowance 249 * (249 : ℝ) ≤ rankSymmetric256Coercivity 249 * (249 : ℝ)^2 * rankSymmetric256IntegralWeight 249) ∧
    (((2*(249 : ℝ)^2+3*249-2) * rankSymmetric256IntegralWeight (249-1) +
      2 * rankSymmetric256RootAllowance 249 * (249 : ℝ) ≤ (249 : ℝ)^2 * rankSymmetric256CumulantWeight 249)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset249, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_250 :
    (rankSymmetric256IntegralWeight (250-1) * rankSymmetric256Convolution 250 ≤ (rankSymmetric256RootAllowance 250)^2) ∧
    (((4*rankSymmetric256Parameter 250-2)*(250 : ℝ)^2+(8*rankSymmetric256Parameter 250-5)*250-2) * rankSymmetric256IntegralWeight (250-1) +
      2 * rankSymmetric256RootAllowance 250 * (250 : ℝ) ≤ rankSymmetric256Coercivity 250 * (250 : ℝ)^2 * rankSymmetric256IntegralWeight 250) ∧
    (((2*(250 : ℝ)^2+3*250-2) * rankSymmetric256IntegralWeight (250-1) +
      2 * rankSymmetric256RootAllowance 250 * (250 : ℝ) ≤ (250 : ℝ)^2 * rankSymmetric256CumulantWeight 250)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset250, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_251 :
    (rankSymmetric256IntegralWeight (251-1) * rankSymmetric256Convolution 251 ≤ (rankSymmetric256RootAllowance 251)^2) ∧
    (((4*rankSymmetric256Parameter 251-2)*(251 : ℝ)^2+(8*rankSymmetric256Parameter 251-5)*251-2) * rankSymmetric256IntegralWeight (251-1) +
      2 * rankSymmetric256RootAllowance 251 * (251 : ℝ) ≤ rankSymmetric256Coercivity 251 * (251 : ℝ)^2 * rankSymmetric256IntegralWeight 251) ∧
    (((2*(251 : ℝ)^2+3*251-2) * rankSymmetric256IntegralWeight (251-1) +
      2 * rankSymmetric256RootAllowance 251 * (251 : ℝ) ≤ (251 : ℝ)^2 * rankSymmetric256CumulantWeight 251)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset251, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_252 :
    (rankSymmetric256IntegralWeight (252-1) * rankSymmetric256Convolution 252 ≤ (rankSymmetric256RootAllowance 252)^2) ∧
    (((4*rankSymmetric256Parameter 252-2)*(252 : ℝ)^2+(8*rankSymmetric256Parameter 252-5)*252-2) * rankSymmetric256IntegralWeight (252-1) +
      2 * rankSymmetric256RootAllowance 252 * (252 : ℝ) ≤ rankSymmetric256Coercivity 252 * (252 : ℝ)^2 * rankSymmetric256IntegralWeight 252) ∧
    (((2*(252 : ℝ)^2+3*252-2) * rankSymmetric256IntegralWeight (252-1) +
      2 * rankSymmetric256RootAllowance 252 * (252 : ℝ) ≤ (252 : ℝ)^2 * rankSymmetric256CumulantWeight 252)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset252, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_253 :
    (rankSymmetric256IntegralWeight (253-1) * rankSymmetric256Convolution 253 ≤ (rankSymmetric256RootAllowance 253)^2) ∧
    (((4*rankSymmetric256Parameter 253-2)*(253 : ℝ)^2+(8*rankSymmetric256Parameter 253-5)*253-2) * rankSymmetric256IntegralWeight (253-1) +
      2 * rankSymmetric256RootAllowance 253 * (253 : ℝ) ≤ rankSymmetric256Coercivity 253 * (253 : ℝ)^2 * rankSymmetric256IntegralWeight 253) ∧
    (((2*(253 : ℝ)^2+3*253-2) * rankSymmetric256IntegralWeight (253-1) +
      2 * rankSymmetric256RootAllowance 253 * (253 : ℝ) ≤ (253 : ℝ)^2 * rankSymmetric256CumulantWeight 253)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset253, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_254 :
    (rankSymmetric256IntegralWeight (254-1) * rankSymmetric256Convolution 254 ≤ (rankSymmetric256RootAllowance 254)^2) ∧
    (((4*rankSymmetric256Parameter 254-2)*(254 : ℝ)^2+(8*rankSymmetric256Parameter 254-5)*254-2) * rankSymmetric256IntegralWeight (254-1) +
      2 * rankSymmetric256RootAllowance 254 * (254 : ℝ) ≤ rankSymmetric256Coercivity 254 * (254 : ℝ)^2 * rankSymmetric256IntegralWeight 254) ∧
    (((2*(254 : ℝ)^2+3*254-2) * rankSymmetric256IntegralWeight (254-1) +
      2 * rankSymmetric256RootAllowance 254 * (254 : ℝ) ≤ (254 : ℝ)^2 * rankSymmetric256CumulantWeight 254)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset254, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_255 :
    (rankSymmetric256IntegralWeight (255-1) * rankSymmetric256Convolution 255 ≤ (rankSymmetric256RootAllowance 255)^2) ∧
    (((4*rankSymmetric256Parameter 255-2)*(255 : ℝ)^2+(8*rankSymmetric256Parameter 255-5)*255-2) * rankSymmetric256IntegralWeight (255-1) +
      2 * rankSymmetric256RootAllowance 255 * (255 : ℝ) ≤ rankSymmetric256Coercivity 255 * (255 : ℝ)^2 * rankSymmetric256IntegralWeight 255) ∧
    (((2*(255 : ℝ)^2+3*255-2) * rankSymmetric256IntegralWeight (255-1) +
      2 * rankSymmetric256RootAllowance 255 * (255 : ℝ) ≤ (255 : ℝ)^2 * rankSymmetric256CumulantWeight 255)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset255, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_256 :
    (rankSymmetric256IntegralWeight (256-1) * rankSymmetric256Convolution 256 ≤ (rankSymmetric256RootAllowance 256)^2) ∧
    (((4*rankSymmetric256Parameter 256-2)*(256 : ℝ)^2+(8*rankSymmetric256Parameter 256-5)*256-2) * rankSymmetric256IntegralWeight (256-1) +
      2 * rankSymmetric256RootAllowance 256 * (256 : ℝ) ≤ rankSymmetric256Coercivity 256 * (256 : ℝ)^2 * rankSymmetric256IntegralWeight 256) ∧
    (((2*(256 : ℝ)^2+3*256-2) * rankSymmetric256IntegralWeight (256-1) +
      2 * rankSymmetric256RootAllowance 256 * (256 : ℝ) ≤ (256 : ℝ)^2 * rankSymmetric256CumulantWeight 256)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset256, Finset.sum_Icc_succ_top]

end KLS.RouteArithmetic
end

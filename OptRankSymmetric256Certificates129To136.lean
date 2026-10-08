import OptRankSymmetric256Weights

set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
noncomputable section
namespace KLS.RouteArithmetic

theorem rankSymmetric256Certificate_129 :
    (rankSymmetric256IntegralWeight (129-1) * rankSymmetric256Convolution 129 ≤ (rankSymmetric256RootAllowance 129)^2) ∧
    (((4*rankSymmetric256Parameter 129-2)*(129 : ℝ)^2+(8*rankSymmetric256Parameter 129-5)*129-2) * rankSymmetric256IntegralWeight (129-1) +
      2 * rankSymmetric256RootAllowance 129 * (129 : ℝ) ≤ rankSymmetric256Coercivity 129 * (129 : ℝ)^2 * rankSymmetric256IntegralWeight 129) ∧
    (((2*(129 : ℝ)^2+3*129-2) * rankSymmetric256IntegralWeight (129-1) +
      2 * rankSymmetric256RootAllowance 129 * (129 : ℝ) ≤ (129 : ℝ)^2 * rankSymmetric256CumulantWeight 129)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset129, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_130 :
    (rankSymmetric256IntegralWeight (130-1) * rankSymmetric256Convolution 130 ≤ (rankSymmetric256RootAllowance 130)^2) ∧
    (((4*rankSymmetric256Parameter 130-2)*(130 : ℝ)^2+(8*rankSymmetric256Parameter 130-5)*130-2) * rankSymmetric256IntegralWeight (130-1) +
      2 * rankSymmetric256RootAllowance 130 * (130 : ℝ) ≤ rankSymmetric256Coercivity 130 * (130 : ℝ)^2 * rankSymmetric256IntegralWeight 130) ∧
    (((2*(130 : ℝ)^2+3*130-2) * rankSymmetric256IntegralWeight (130-1) +
      2 * rankSymmetric256RootAllowance 130 * (130 : ℝ) ≤ (130 : ℝ)^2 * rankSymmetric256CumulantWeight 130)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset130, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_131 :
    (rankSymmetric256IntegralWeight (131-1) * rankSymmetric256Convolution 131 ≤ (rankSymmetric256RootAllowance 131)^2) ∧
    (((4*rankSymmetric256Parameter 131-2)*(131 : ℝ)^2+(8*rankSymmetric256Parameter 131-5)*131-2) * rankSymmetric256IntegralWeight (131-1) +
      2 * rankSymmetric256RootAllowance 131 * (131 : ℝ) ≤ rankSymmetric256Coercivity 131 * (131 : ℝ)^2 * rankSymmetric256IntegralWeight 131) ∧
    (((2*(131 : ℝ)^2+3*131-2) * rankSymmetric256IntegralWeight (131-1) +
      2 * rankSymmetric256RootAllowance 131 * (131 : ℝ) ≤ (131 : ℝ)^2 * rankSymmetric256CumulantWeight 131)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset131, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_132 :
    (rankSymmetric256IntegralWeight (132-1) * rankSymmetric256Convolution 132 ≤ (rankSymmetric256RootAllowance 132)^2) ∧
    (((4*rankSymmetric256Parameter 132-2)*(132 : ℝ)^2+(8*rankSymmetric256Parameter 132-5)*132-2) * rankSymmetric256IntegralWeight (132-1) +
      2 * rankSymmetric256RootAllowance 132 * (132 : ℝ) ≤ rankSymmetric256Coercivity 132 * (132 : ℝ)^2 * rankSymmetric256IntegralWeight 132) ∧
    (((2*(132 : ℝ)^2+3*132-2) * rankSymmetric256IntegralWeight (132-1) +
      2 * rankSymmetric256RootAllowance 132 * (132 : ℝ) ≤ (132 : ℝ)^2 * rankSymmetric256CumulantWeight 132)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset132, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_133 :
    (rankSymmetric256IntegralWeight (133-1) * rankSymmetric256Convolution 133 ≤ (rankSymmetric256RootAllowance 133)^2) ∧
    (((4*rankSymmetric256Parameter 133-2)*(133 : ℝ)^2+(8*rankSymmetric256Parameter 133-5)*133-2) * rankSymmetric256IntegralWeight (133-1) +
      2 * rankSymmetric256RootAllowance 133 * (133 : ℝ) ≤ rankSymmetric256Coercivity 133 * (133 : ℝ)^2 * rankSymmetric256IntegralWeight 133) ∧
    (((2*(133 : ℝ)^2+3*133-2) * rankSymmetric256IntegralWeight (133-1) +
      2 * rankSymmetric256RootAllowance 133 * (133 : ℝ) ≤ (133 : ℝ)^2 * rankSymmetric256CumulantWeight 133)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset133, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_134 :
    (rankSymmetric256IntegralWeight (134-1) * rankSymmetric256Convolution 134 ≤ (rankSymmetric256RootAllowance 134)^2) ∧
    (((4*rankSymmetric256Parameter 134-2)*(134 : ℝ)^2+(8*rankSymmetric256Parameter 134-5)*134-2) * rankSymmetric256IntegralWeight (134-1) +
      2 * rankSymmetric256RootAllowance 134 * (134 : ℝ) ≤ rankSymmetric256Coercivity 134 * (134 : ℝ)^2 * rankSymmetric256IntegralWeight 134) ∧
    (((2*(134 : ℝ)^2+3*134-2) * rankSymmetric256IntegralWeight (134-1) +
      2 * rankSymmetric256RootAllowance 134 * (134 : ℝ) ≤ (134 : ℝ)^2 * rankSymmetric256CumulantWeight 134)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset134, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_135 :
    (rankSymmetric256IntegralWeight (135-1) * rankSymmetric256Convolution 135 ≤ (rankSymmetric256RootAllowance 135)^2) ∧
    (((4*rankSymmetric256Parameter 135-2)*(135 : ℝ)^2+(8*rankSymmetric256Parameter 135-5)*135-2) * rankSymmetric256IntegralWeight (135-1) +
      2 * rankSymmetric256RootAllowance 135 * (135 : ℝ) ≤ rankSymmetric256Coercivity 135 * (135 : ℝ)^2 * rankSymmetric256IntegralWeight 135) ∧
    (((2*(135 : ℝ)^2+3*135-2) * rankSymmetric256IntegralWeight (135-1) +
      2 * rankSymmetric256RootAllowance 135 * (135 : ℝ) ≤ (135 : ℝ)^2 * rankSymmetric256CumulantWeight 135)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset135, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_136 :
    (rankSymmetric256IntegralWeight (136-1) * rankSymmetric256Convolution 136 ≤ (rankSymmetric256RootAllowance 136)^2) ∧
    (((4*rankSymmetric256Parameter 136-2)*(136 : ℝ)^2+(8*rankSymmetric256Parameter 136-5)*136-2) * rankSymmetric256IntegralWeight (136-1) +
      2 * rankSymmetric256RootAllowance 136 * (136 : ℝ) ≤ rankSymmetric256Coercivity 136 * (136 : ℝ)^2 * rankSymmetric256IntegralWeight 136) ∧
    (((2*(136 : ℝ)^2+3*136-2) * rankSymmetric256IntegralWeight (136-1) +
      2 * rankSymmetric256RootAllowance 136 * (136 : ℝ) ≤ (136 : ℝ)^2 * rankSymmetric256CumulantWeight 136)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset136, Finset.sum_Icc_succ_top]

end KLS.RouteArithmetic
end

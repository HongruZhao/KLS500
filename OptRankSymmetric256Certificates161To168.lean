import OptRankSymmetric256Weights

set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
noncomputable section
namespace KLS.RouteArithmetic

theorem rankSymmetric256Certificate_161 :
    (rankSymmetric256IntegralWeight (161-1) * rankSymmetric256Convolution 161 ≤ (rankSymmetric256RootAllowance 161)^2) ∧
    (((4*rankSymmetric256Parameter 161-2)*(161 : ℝ)^2+(8*rankSymmetric256Parameter 161-5)*161-2) * rankSymmetric256IntegralWeight (161-1) +
      2 * rankSymmetric256RootAllowance 161 * (161 : ℝ) ≤ rankSymmetric256Coercivity 161 * (161 : ℝ)^2 * rankSymmetric256IntegralWeight 161) ∧
    (((2*(161 : ℝ)^2+3*161-2) * rankSymmetric256IntegralWeight (161-1) +
      2 * rankSymmetric256RootAllowance 161 * (161 : ℝ) ≤ (161 : ℝ)^2 * rankSymmetric256CumulantWeight 161)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset161, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_162 :
    (rankSymmetric256IntegralWeight (162-1) * rankSymmetric256Convolution 162 ≤ (rankSymmetric256RootAllowance 162)^2) ∧
    (((4*rankSymmetric256Parameter 162-2)*(162 : ℝ)^2+(8*rankSymmetric256Parameter 162-5)*162-2) * rankSymmetric256IntegralWeight (162-1) +
      2 * rankSymmetric256RootAllowance 162 * (162 : ℝ) ≤ rankSymmetric256Coercivity 162 * (162 : ℝ)^2 * rankSymmetric256IntegralWeight 162) ∧
    (((2*(162 : ℝ)^2+3*162-2) * rankSymmetric256IntegralWeight (162-1) +
      2 * rankSymmetric256RootAllowance 162 * (162 : ℝ) ≤ (162 : ℝ)^2 * rankSymmetric256CumulantWeight 162)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset162, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_163 :
    (rankSymmetric256IntegralWeight (163-1) * rankSymmetric256Convolution 163 ≤ (rankSymmetric256RootAllowance 163)^2) ∧
    (((4*rankSymmetric256Parameter 163-2)*(163 : ℝ)^2+(8*rankSymmetric256Parameter 163-5)*163-2) * rankSymmetric256IntegralWeight (163-1) +
      2 * rankSymmetric256RootAllowance 163 * (163 : ℝ) ≤ rankSymmetric256Coercivity 163 * (163 : ℝ)^2 * rankSymmetric256IntegralWeight 163) ∧
    (((2*(163 : ℝ)^2+3*163-2) * rankSymmetric256IntegralWeight (163-1) +
      2 * rankSymmetric256RootAllowance 163 * (163 : ℝ) ≤ (163 : ℝ)^2 * rankSymmetric256CumulantWeight 163)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset163, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_164 :
    (rankSymmetric256IntegralWeight (164-1) * rankSymmetric256Convolution 164 ≤ (rankSymmetric256RootAllowance 164)^2) ∧
    (((4*rankSymmetric256Parameter 164-2)*(164 : ℝ)^2+(8*rankSymmetric256Parameter 164-5)*164-2) * rankSymmetric256IntegralWeight (164-1) +
      2 * rankSymmetric256RootAllowance 164 * (164 : ℝ) ≤ rankSymmetric256Coercivity 164 * (164 : ℝ)^2 * rankSymmetric256IntegralWeight 164) ∧
    (((2*(164 : ℝ)^2+3*164-2) * rankSymmetric256IntegralWeight (164-1) +
      2 * rankSymmetric256RootAllowance 164 * (164 : ℝ) ≤ (164 : ℝ)^2 * rankSymmetric256CumulantWeight 164)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset164, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_165 :
    (rankSymmetric256IntegralWeight (165-1) * rankSymmetric256Convolution 165 ≤ (rankSymmetric256RootAllowance 165)^2) ∧
    (((4*rankSymmetric256Parameter 165-2)*(165 : ℝ)^2+(8*rankSymmetric256Parameter 165-5)*165-2) * rankSymmetric256IntegralWeight (165-1) +
      2 * rankSymmetric256RootAllowance 165 * (165 : ℝ) ≤ rankSymmetric256Coercivity 165 * (165 : ℝ)^2 * rankSymmetric256IntegralWeight 165) ∧
    (((2*(165 : ℝ)^2+3*165-2) * rankSymmetric256IntegralWeight (165-1) +
      2 * rankSymmetric256RootAllowance 165 * (165 : ℝ) ≤ (165 : ℝ)^2 * rankSymmetric256CumulantWeight 165)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset165, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_166 :
    (rankSymmetric256IntegralWeight (166-1) * rankSymmetric256Convolution 166 ≤ (rankSymmetric256RootAllowance 166)^2) ∧
    (((4*rankSymmetric256Parameter 166-2)*(166 : ℝ)^2+(8*rankSymmetric256Parameter 166-5)*166-2) * rankSymmetric256IntegralWeight (166-1) +
      2 * rankSymmetric256RootAllowance 166 * (166 : ℝ) ≤ rankSymmetric256Coercivity 166 * (166 : ℝ)^2 * rankSymmetric256IntegralWeight 166) ∧
    (((2*(166 : ℝ)^2+3*166-2) * rankSymmetric256IntegralWeight (166-1) +
      2 * rankSymmetric256RootAllowance 166 * (166 : ℝ) ≤ (166 : ℝ)^2 * rankSymmetric256CumulantWeight 166)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset166, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_167 :
    (rankSymmetric256IntegralWeight (167-1) * rankSymmetric256Convolution 167 ≤ (rankSymmetric256RootAllowance 167)^2) ∧
    (((4*rankSymmetric256Parameter 167-2)*(167 : ℝ)^2+(8*rankSymmetric256Parameter 167-5)*167-2) * rankSymmetric256IntegralWeight (167-1) +
      2 * rankSymmetric256RootAllowance 167 * (167 : ℝ) ≤ rankSymmetric256Coercivity 167 * (167 : ℝ)^2 * rankSymmetric256IntegralWeight 167) ∧
    (((2*(167 : ℝ)^2+3*167-2) * rankSymmetric256IntegralWeight (167-1) +
      2 * rankSymmetric256RootAllowance 167 * (167 : ℝ) ≤ (167 : ℝ)^2 * rankSymmetric256CumulantWeight 167)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset167, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_168 :
    (rankSymmetric256IntegralWeight (168-1) * rankSymmetric256Convolution 168 ≤ (rankSymmetric256RootAllowance 168)^2) ∧
    (((4*rankSymmetric256Parameter 168-2)*(168 : ℝ)^2+(8*rankSymmetric256Parameter 168-5)*168-2) * rankSymmetric256IntegralWeight (168-1) +
      2 * rankSymmetric256RootAllowance 168 * (168 : ℝ) ≤ rankSymmetric256Coercivity 168 * (168 : ℝ)^2 * rankSymmetric256IntegralWeight 168) ∧
    (((2*(168 : ℝ)^2+3*168-2) * rankSymmetric256IntegralWeight (168-1) +
      2 * rankSymmetric256RootAllowance 168 * (168 : ℝ) ≤ (168 : ℝ)^2 * rankSymmetric256CumulantWeight 168)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset168, Finset.sum_Icc_succ_top]

end KLS.RouteArithmetic
end

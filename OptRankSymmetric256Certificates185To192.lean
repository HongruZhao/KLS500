import OptRankSymmetric256Weights

set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
noncomputable section
namespace KLS.RouteArithmetic

theorem rankSymmetric256Certificate_185 :
    (rankSymmetric256IntegralWeight (185-1) * rankSymmetric256Convolution 185 ≤ (rankSymmetric256RootAllowance 185)^2) ∧
    (((4*rankSymmetric256Parameter 185-2)*(185 : ℝ)^2+(8*rankSymmetric256Parameter 185-5)*185-2) * rankSymmetric256IntegralWeight (185-1) +
      2 * rankSymmetric256RootAllowance 185 * (185 : ℝ) ≤ rankSymmetric256Coercivity 185 * (185 : ℝ)^2 * rankSymmetric256IntegralWeight 185) ∧
    (((2*(185 : ℝ)^2+3*185-2) * rankSymmetric256IntegralWeight (185-1) +
      2 * rankSymmetric256RootAllowance 185 * (185 : ℝ) ≤ (185 : ℝ)^2 * rankSymmetric256CumulantWeight 185)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset185, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_186 :
    (rankSymmetric256IntegralWeight (186-1) * rankSymmetric256Convolution 186 ≤ (rankSymmetric256RootAllowance 186)^2) ∧
    (((4*rankSymmetric256Parameter 186-2)*(186 : ℝ)^2+(8*rankSymmetric256Parameter 186-5)*186-2) * rankSymmetric256IntegralWeight (186-1) +
      2 * rankSymmetric256RootAllowance 186 * (186 : ℝ) ≤ rankSymmetric256Coercivity 186 * (186 : ℝ)^2 * rankSymmetric256IntegralWeight 186) ∧
    (((2*(186 : ℝ)^2+3*186-2) * rankSymmetric256IntegralWeight (186-1) +
      2 * rankSymmetric256RootAllowance 186 * (186 : ℝ) ≤ (186 : ℝ)^2 * rankSymmetric256CumulantWeight 186)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset186, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_187 :
    (rankSymmetric256IntegralWeight (187-1) * rankSymmetric256Convolution 187 ≤ (rankSymmetric256RootAllowance 187)^2) ∧
    (((4*rankSymmetric256Parameter 187-2)*(187 : ℝ)^2+(8*rankSymmetric256Parameter 187-5)*187-2) * rankSymmetric256IntegralWeight (187-1) +
      2 * rankSymmetric256RootAllowance 187 * (187 : ℝ) ≤ rankSymmetric256Coercivity 187 * (187 : ℝ)^2 * rankSymmetric256IntegralWeight 187) ∧
    (((2*(187 : ℝ)^2+3*187-2) * rankSymmetric256IntegralWeight (187-1) +
      2 * rankSymmetric256RootAllowance 187 * (187 : ℝ) ≤ (187 : ℝ)^2 * rankSymmetric256CumulantWeight 187)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset187, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_188 :
    (rankSymmetric256IntegralWeight (188-1) * rankSymmetric256Convolution 188 ≤ (rankSymmetric256RootAllowance 188)^2) ∧
    (((4*rankSymmetric256Parameter 188-2)*(188 : ℝ)^2+(8*rankSymmetric256Parameter 188-5)*188-2) * rankSymmetric256IntegralWeight (188-1) +
      2 * rankSymmetric256RootAllowance 188 * (188 : ℝ) ≤ rankSymmetric256Coercivity 188 * (188 : ℝ)^2 * rankSymmetric256IntegralWeight 188) ∧
    (((2*(188 : ℝ)^2+3*188-2) * rankSymmetric256IntegralWeight (188-1) +
      2 * rankSymmetric256RootAllowance 188 * (188 : ℝ) ≤ (188 : ℝ)^2 * rankSymmetric256CumulantWeight 188)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset188, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_189 :
    (rankSymmetric256IntegralWeight (189-1) * rankSymmetric256Convolution 189 ≤ (rankSymmetric256RootAllowance 189)^2) ∧
    (((4*rankSymmetric256Parameter 189-2)*(189 : ℝ)^2+(8*rankSymmetric256Parameter 189-5)*189-2) * rankSymmetric256IntegralWeight (189-1) +
      2 * rankSymmetric256RootAllowance 189 * (189 : ℝ) ≤ rankSymmetric256Coercivity 189 * (189 : ℝ)^2 * rankSymmetric256IntegralWeight 189) ∧
    (((2*(189 : ℝ)^2+3*189-2) * rankSymmetric256IntegralWeight (189-1) +
      2 * rankSymmetric256RootAllowance 189 * (189 : ℝ) ≤ (189 : ℝ)^2 * rankSymmetric256CumulantWeight 189)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset189, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_190 :
    (rankSymmetric256IntegralWeight (190-1) * rankSymmetric256Convolution 190 ≤ (rankSymmetric256RootAllowance 190)^2) ∧
    (((4*rankSymmetric256Parameter 190-2)*(190 : ℝ)^2+(8*rankSymmetric256Parameter 190-5)*190-2) * rankSymmetric256IntegralWeight (190-1) +
      2 * rankSymmetric256RootAllowance 190 * (190 : ℝ) ≤ rankSymmetric256Coercivity 190 * (190 : ℝ)^2 * rankSymmetric256IntegralWeight 190) ∧
    (((2*(190 : ℝ)^2+3*190-2) * rankSymmetric256IntegralWeight (190-1) +
      2 * rankSymmetric256RootAllowance 190 * (190 : ℝ) ≤ (190 : ℝ)^2 * rankSymmetric256CumulantWeight 190)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset190, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_191 :
    (rankSymmetric256IntegralWeight (191-1) * rankSymmetric256Convolution 191 ≤ (rankSymmetric256RootAllowance 191)^2) ∧
    (((4*rankSymmetric256Parameter 191-2)*(191 : ℝ)^2+(8*rankSymmetric256Parameter 191-5)*191-2) * rankSymmetric256IntegralWeight (191-1) +
      2 * rankSymmetric256RootAllowance 191 * (191 : ℝ) ≤ rankSymmetric256Coercivity 191 * (191 : ℝ)^2 * rankSymmetric256IntegralWeight 191) ∧
    (((2*(191 : ℝ)^2+3*191-2) * rankSymmetric256IntegralWeight (191-1) +
      2 * rankSymmetric256RootAllowance 191 * (191 : ℝ) ≤ (191 : ℝ)^2 * rankSymmetric256CumulantWeight 191)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset191, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_192 :
    (rankSymmetric256IntegralWeight (192-1) * rankSymmetric256Convolution 192 ≤ (rankSymmetric256RootAllowance 192)^2) ∧
    (((4*rankSymmetric256Parameter 192-2)*(192 : ℝ)^2+(8*rankSymmetric256Parameter 192-5)*192-2) * rankSymmetric256IntegralWeight (192-1) +
      2 * rankSymmetric256RootAllowance 192 * (192 : ℝ) ≤ rankSymmetric256Coercivity 192 * (192 : ℝ)^2 * rankSymmetric256IntegralWeight 192) ∧
    (((2*(192 : ℝ)^2+3*192-2) * rankSymmetric256IntegralWeight (192-1) +
      2 * rankSymmetric256RootAllowance 192 * (192 : ℝ) ≤ (192 : ℝ)^2 * rankSymmetric256CumulantWeight 192)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset192, Finset.sum_Icc_succ_top]

end KLS.RouteArithmetic
end

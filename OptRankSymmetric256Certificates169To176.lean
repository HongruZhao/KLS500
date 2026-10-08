import OptRankSymmetric256Weights

set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
noncomputable section
namespace KLS.RouteArithmetic

theorem rankSymmetric256Certificate_169 :
    (rankSymmetric256IntegralWeight (169-1) * rankSymmetric256Convolution 169 ≤ (rankSymmetric256RootAllowance 169)^2) ∧
    (((4*rankSymmetric256Parameter 169-2)*(169 : ℝ)^2+(8*rankSymmetric256Parameter 169-5)*169-2) * rankSymmetric256IntegralWeight (169-1) +
      2 * rankSymmetric256RootAllowance 169 * (169 : ℝ) ≤ rankSymmetric256Coercivity 169 * (169 : ℝ)^2 * rankSymmetric256IntegralWeight 169) ∧
    (((2*(169 : ℝ)^2+3*169-2) * rankSymmetric256IntegralWeight (169-1) +
      2 * rankSymmetric256RootAllowance 169 * (169 : ℝ) ≤ (169 : ℝ)^2 * rankSymmetric256CumulantWeight 169)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset169, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_170 :
    (rankSymmetric256IntegralWeight (170-1) * rankSymmetric256Convolution 170 ≤ (rankSymmetric256RootAllowance 170)^2) ∧
    (((4*rankSymmetric256Parameter 170-2)*(170 : ℝ)^2+(8*rankSymmetric256Parameter 170-5)*170-2) * rankSymmetric256IntegralWeight (170-1) +
      2 * rankSymmetric256RootAllowance 170 * (170 : ℝ) ≤ rankSymmetric256Coercivity 170 * (170 : ℝ)^2 * rankSymmetric256IntegralWeight 170) ∧
    (((2*(170 : ℝ)^2+3*170-2) * rankSymmetric256IntegralWeight (170-1) +
      2 * rankSymmetric256RootAllowance 170 * (170 : ℝ) ≤ (170 : ℝ)^2 * rankSymmetric256CumulantWeight 170)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset170, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_171 :
    (rankSymmetric256IntegralWeight (171-1) * rankSymmetric256Convolution 171 ≤ (rankSymmetric256RootAllowance 171)^2) ∧
    (((4*rankSymmetric256Parameter 171-2)*(171 : ℝ)^2+(8*rankSymmetric256Parameter 171-5)*171-2) * rankSymmetric256IntegralWeight (171-1) +
      2 * rankSymmetric256RootAllowance 171 * (171 : ℝ) ≤ rankSymmetric256Coercivity 171 * (171 : ℝ)^2 * rankSymmetric256IntegralWeight 171) ∧
    (((2*(171 : ℝ)^2+3*171-2) * rankSymmetric256IntegralWeight (171-1) +
      2 * rankSymmetric256RootAllowance 171 * (171 : ℝ) ≤ (171 : ℝ)^2 * rankSymmetric256CumulantWeight 171)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset171, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_172 :
    (rankSymmetric256IntegralWeight (172-1) * rankSymmetric256Convolution 172 ≤ (rankSymmetric256RootAllowance 172)^2) ∧
    (((4*rankSymmetric256Parameter 172-2)*(172 : ℝ)^2+(8*rankSymmetric256Parameter 172-5)*172-2) * rankSymmetric256IntegralWeight (172-1) +
      2 * rankSymmetric256RootAllowance 172 * (172 : ℝ) ≤ rankSymmetric256Coercivity 172 * (172 : ℝ)^2 * rankSymmetric256IntegralWeight 172) ∧
    (((2*(172 : ℝ)^2+3*172-2) * rankSymmetric256IntegralWeight (172-1) +
      2 * rankSymmetric256RootAllowance 172 * (172 : ℝ) ≤ (172 : ℝ)^2 * rankSymmetric256CumulantWeight 172)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset172, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_173 :
    (rankSymmetric256IntegralWeight (173-1) * rankSymmetric256Convolution 173 ≤ (rankSymmetric256RootAllowance 173)^2) ∧
    (((4*rankSymmetric256Parameter 173-2)*(173 : ℝ)^2+(8*rankSymmetric256Parameter 173-5)*173-2) * rankSymmetric256IntegralWeight (173-1) +
      2 * rankSymmetric256RootAllowance 173 * (173 : ℝ) ≤ rankSymmetric256Coercivity 173 * (173 : ℝ)^2 * rankSymmetric256IntegralWeight 173) ∧
    (((2*(173 : ℝ)^2+3*173-2) * rankSymmetric256IntegralWeight (173-1) +
      2 * rankSymmetric256RootAllowance 173 * (173 : ℝ) ≤ (173 : ℝ)^2 * rankSymmetric256CumulantWeight 173)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset173, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_174 :
    (rankSymmetric256IntegralWeight (174-1) * rankSymmetric256Convolution 174 ≤ (rankSymmetric256RootAllowance 174)^2) ∧
    (((4*rankSymmetric256Parameter 174-2)*(174 : ℝ)^2+(8*rankSymmetric256Parameter 174-5)*174-2) * rankSymmetric256IntegralWeight (174-1) +
      2 * rankSymmetric256RootAllowance 174 * (174 : ℝ) ≤ rankSymmetric256Coercivity 174 * (174 : ℝ)^2 * rankSymmetric256IntegralWeight 174) ∧
    (((2*(174 : ℝ)^2+3*174-2) * rankSymmetric256IntegralWeight (174-1) +
      2 * rankSymmetric256RootAllowance 174 * (174 : ℝ) ≤ (174 : ℝ)^2 * rankSymmetric256CumulantWeight 174)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset174, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_175 :
    (rankSymmetric256IntegralWeight (175-1) * rankSymmetric256Convolution 175 ≤ (rankSymmetric256RootAllowance 175)^2) ∧
    (((4*rankSymmetric256Parameter 175-2)*(175 : ℝ)^2+(8*rankSymmetric256Parameter 175-5)*175-2) * rankSymmetric256IntegralWeight (175-1) +
      2 * rankSymmetric256RootAllowance 175 * (175 : ℝ) ≤ rankSymmetric256Coercivity 175 * (175 : ℝ)^2 * rankSymmetric256IntegralWeight 175) ∧
    (((2*(175 : ℝ)^2+3*175-2) * rankSymmetric256IntegralWeight (175-1) +
      2 * rankSymmetric256RootAllowance 175 * (175 : ℝ) ≤ (175 : ℝ)^2 * rankSymmetric256CumulantWeight 175)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset175, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_176 :
    (rankSymmetric256IntegralWeight (176-1) * rankSymmetric256Convolution 176 ≤ (rankSymmetric256RootAllowance 176)^2) ∧
    (((4*rankSymmetric256Parameter 176-2)*(176 : ℝ)^2+(8*rankSymmetric256Parameter 176-5)*176-2) * rankSymmetric256IntegralWeight (176-1) +
      2 * rankSymmetric256RootAllowance 176 * (176 : ℝ) ≤ rankSymmetric256Coercivity 176 * (176 : ℝ)^2 * rankSymmetric256IntegralWeight 176) ∧
    (((2*(176 : ℝ)^2+3*176-2) * rankSymmetric256IntegralWeight (176-1) +
      2 * rankSymmetric256RootAllowance 176 * (176 : ℝ) ≤ (176 : ℝ)^2 * rankSymmetric256CumulantWeight 176)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset176, Finset.sum_Icc_succ_top]

end KLS.RouteArithmetic
end

import OptRankSymmetric256Weights

set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
noncomputable section
namespace KLS.RouteArithmetic

theorem rankSymmetric256Certificate_145 :
    (rankSymmetric256IntegralWeight (145-1) * rankSymmetric256Convolution 145 ≤ (rankSymmetric256RootAllowance 145)^2) ∧
    (((4*rankSymmetric256Parameter 145-2)*(145 : ℝ)^2+(8*rankSymmetric256Parameter 145-5)*145-2) * rankSymmetric256IntegralWeight (145-1) +
      2 * rankSymmetric256RootAllowance 145 * (145 : ℝ) ≤ rankSymmetric256Coercivity 145 * (145 : ℝ)^2 * rankSymmetric256IntegralWeight 145) ∧
    (((2*(145 : ℝ)^2+3*145-2) * rankSymmetric256IntegralWeight (145-1) +
      2 * rankSymmetric256RootAllowance 145 * (145 : ℝ) ≤ (145 : ℝ)^2 * rankSymmetric256CumulantWeight 145)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset145, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_146 :
    (rankSymmetric256IntegralWeight (146-1) * rankSymmetric256Convolution 146 ≤ (rankSymmetric256RootAllowance 146)^2) ∧
    (((4*rankSymmetric256Parameter 146-2)*(146 : ℝ)^2+(8*rankSymmetric256Parameter 146-5)*146-2) * rankSymmetric256IntegralWeight (146-1) +
      2 * rankSymmetric256RootAllowance 146 * (146 : ℝ) ≤ rankSymmetric256Coercivity 146 * (146 : ℝ)^2 * rankSymmetric256IntegralWeight 146) ∧
    (((2*(146 : ℝ)^2+3*146-2) * rankSymmetric256IntegralWeight (146-1) +
      2 * rankSymmetric256RootAllowance 146 * (146 : ℝ) ≤ (146 : ℝ)^2 * rankSymmetric256CumulantWeight 146)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset146, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_147 :
    (rankSymmetric256IntegralWeight (147-1) * rankSymmetric256Convolution 147 ≤ (rankSymmetric256RootAllowance 147)^2) ∧
    (((4*rankSymmetric256Parameter 147-2)*(147 : ℝ)^2+(8*rankSymmetric256Parameter 147-5)*147-2) * rankSymmetric256IntegralWeight (147-1) +
      2 * rankSymmetric256RootAllowance 147 * (147 : ℝ) ≤ rankSymmetric256Coercivity 147 * (147 : ℝ)^2 * rankSymmetric256IntegralWeight 147) ∧
    (((2*(147 : ℝ)^2+3*147-2) * rankSymmetric256IntegralWeight (147-1) +
      2 * rankSymmetric256RootAllowance 147 * (147 : ℝ) ≤ (147 : ℝ)^2 * rankSymmetric256CumulantWeight 147)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset147, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_148 :
    (rankSymmetric256IntegralWeight (148-1) * rankSymmetric256Convolution 148 ≤ (rankSymmetric256RootAllowance 148)^2) ∧
    (((4*rankSymmetric256Parameter 148-2)*(148 : ℝ)^2+(8*rankSymmetric256Parameter 148-5)*148-2) * rankSymmetric256IntegralWeight (148-1) +
      2 * rankSymmetric256RootAllowance 148 * (148 : ℝ) ≤ rankSymmetric256Coercivity 148 * (148 : ℝ)^2 * rankSymmetric256IntegralWeight 148) ∧
    (((2*(148 : ℝ)^2+3*148-2) * rankSymmetric256IntegralWeight (148-1) +
      2 * rankSymmetric256RootAllowance 148 * (148 : ℝ) ≤ (148 : ℝ)^2 * rankSymmetric256CumulantWeight 148)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset148, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_149 :
    (rankSymmetric256IntegralWeight (149-1) * rankSymmetric256Convolution 149 ≤ (rankSymmetric256RootAllowance 149)^2) ∧
    (((4*rankSymmetric256Parameter 149-2)*(149 : ℝ)^2+(8*rankSymmetric256Parameter 149-5)*149-2) * rankSymmetric256IntegralWeight (149-1) +
      2 * rankSymmetric256RootAllowance 149 * (149 : ℝ) ≤ rankSymmetric256Coercivity 149 * (149 : ℝ)^2 * rankSymmetric256IntegralWeight 149) ∧
    (((2*(149 : ℝ)^2+3*149-2) * rankSymmetric256IntegralWeight (149-1) +
      2 * rankSymmetric256RootAllowance 149 * (149 : ℝ) ≤ (149 : ℝ)^2 * rankSymmetric256CumulantWeight 149)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset149, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_150 :
    (rankSymmetric256IntegralWeight (150-1) * rankSymmetric256Convolution 150 ≤ (rankSymmetric256RootAllowance 150)^2) ∧
    (((4*rankSymmetric256Parameter 150-2)*(150 : ℝ)^2+(8*rankSymmetric256Parameter 150-5)*150-2) * rankSymmetric256IntegralWeight (150-1) +
      2 * rankSymmetric256RootAllowance 150 * (150 : ℝ) ≤ rankSymmetric256Coercivity 150 * (150 : ℝ)^2 * rankSymmetric256IntegralWeight 150) ∧
    (((2*(150 : ℝ)^2+3*150-2) * rankSymmetric256IntegralWeight (150-1) +
      2 * rankSymmetric256RootAllowance 150 * (150 : ℝ) ≤ (150 : ℝ)^2 * rankSymmetric256CumulantWeight 150)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset150, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_151 :
    (rankSymmetric256IntegralWeight (151-1) * rankSymmetric256Convolution 151 ≤ (rankSymmetric256RootAllowance 151)^2) ∧
    (((4*rankSymmetric256Parameter 151-2)*(151 : ℝ)^2+(8*rankSymmetric256Parameter 151-5)*151-2) * rankSymmetric256IntegralWeight (151-1) +
      2 * rankSymmetric256RootAllowance 151 * (151 : ℝ) ≤ rankSymmetric256Coercivity 151 * (151 : ℝ)^2 * rankSymmetric256IntegralWeight 151) ∧
    (((2*(151 : ℝ)^2+3*151-2) * rankSymmetric256IntegralWeight (151-1) +
      2 * rankSymmetric256RootAllowance 151 * (151 : ℝ) ≤ (151 : ℝ)^2 * rankSymmetric256CumulantWeight 151)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset151, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_152 :
    (rankSymmetric256IntegralWeight (152-1) * rankSymmetric256Convolution 152 ≤ (rankSymmetric256RootAllowance 152)^2) ∧
    (((4*rankSymmetric256Parameter 152-2)*(152 : ℝ)^2+(8*rankSymmetric256Parameter 152-5)*152-2) * rankSymmetric256IntegralWeight (152-1) +
      2 * rankSymmetric256RootAllowance 152 * (152 : ℝ) ≤ rankSymmetric256Coercivity 152 * (152 : ℝ)^2 * rankSymmetric256IntegralWeight 152) ∧
    (((2*(152 : ℝ)^2+3*152-2) * rankSymmetric256IntegralWeight (152-1) +
      2 * rankSymmetric256RootAllowance 152 * (152 : ℝ) ≤ (152 : ℝ)^2 * rankSymmetric256CumulantWeight 152)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset152, Finset.sum_Icc_succ_top]

end KLS.RouteArithmetic
end

import OptRankSymmetric256Weights

set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
noncomputable section
namespace KLS.RouteArithmetic

theorem rankSymmetric256Certificate_201 :
    (rankSymmetric256IntegralWeight (201-1) * rankSymmetric256Convolution 201 ≤ (rankSymmetric256RootAllowance 201)^2) ∧
    (((4*rankSymmetric256Parameter 201-2)*(201 : ℝ)^2+(8*rankSymmetric256Parameter 201-5)*201-2) * rankSymmetric256IntegralWeight (201-1) +
      2 * rankSymmetric256RootAllowance 201 * (201 : ℝ) ≤ rankSymmetric256Coercivity 201 * (201 : ℝ)^2 * rankSymmetric256IntegralWeight 201) ∧
    (((2*(201 : ℝ)^2+3*201-2) * rankSymmetric256IntegralWeight (201-1) +
      2 * rankSymmetric256RootAllowance 201 * (201 : ℝ) ≤ (201 : ℝ)^2 * rankSymmetric256CumulantWeight 201)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset201, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_202 :
    (rankSymmetric256IntegralWeight (202-1) * rankSymmetric256Convolution 202 ≤ (rankSymmetric256RootAllowance 202)^2) ∧
    (((4*rankSymmetric256Parameter 202-2)*(202 : ℝ)^2+(8*rankSymmetric256Parameter 202-5)*202-2) * rankSymmetric256IntegralWeight (202-1) +
      2 * rankSymmetric256RootAllowance 202 * (202 : ℝ) ≤ rankSymmetric256Coercivity 202 * (202 : ℝ)^2 * rankSymmetric256IntegralWeight 202) ∧
    (((2*(202 : ℝ)^2+3*202-2) * rankSymmetric256IntegralWeight (202-1) +
      2 * rankSymmetric256RootAllowance 202 * (202 : ℝ) ≤ (202 : ℝ)^2 * rankSymmetric256CumulantWeight 202)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset202, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_203 :
    (rankSymmetric256IntegralWeight (203-1) * rankSymmetric256Convolution 203 ≤ (rankSymmetric256RootAllowance 203)^2) ∧
    (((4*rankSymmetric256Parameter 203-2)*(203 : ℝ)^2+(8*rankSymmetric256Parameter 203-5)*203-2) * rankSymmetric256IntegralWeight (203-1) +
      2 * rankSymmetric256RootAllowance 203 * (203 : ℝ) ≤ rankSymmetric256Coercivity 203 * (203 : ℝ)^2 * rankSymmetric256IntegralWeight 203) ∧
    (((2*(203 : ℝ)^2+3*203-2) * rankSymmetric256IntegralWeight (203-1) +
      2 * rankSymmetric256RootAllowance 203 * (203 : ℝ) ≤ (203 : ℝ)^2 * rankSymmetric256CumulantWeight 203)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset203, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_204 :
    (rankSymmetric256IntegralWeight (204-1) * rankSymmetric256Convolution 204 ≤ (rankSymmetric256RootAllowance 204)^2) ∧
    (((4*rankSymmetric256Parameter 204-2)*(204 : ℝ)^2+(8*rankSymmetric256Parameter 204-5)*204-2) * rankSymmetric256IntegralWeight (204-1) +
      2 * rankSymmetric256RootAllowance 204 * (204 : ℝ) ≤ rankSymmetric256Coercivity 204 * (204 : ℝ)^2 * rankSymmetric256IntegralWeight 204) ∧
    (((2*(204 : ℝ)^2+3*204-2) * rankSymmetric256IntegralWeight (204-1) +
      2 * rankSymmetric256RootAllowance 204 * (204 : ℝ) ≤ (204 : ℝ)^2 * rankSymmetric256CumulantWeight 204)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset204, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_205 :
    (rankSymmetric256IntegralWeight (205-1) * rankSymmetric256Convolution 205 ≤ (rankSymmetric256RootAllowance 205)^2) ∧
    (((4*rankSymmetric256Parameter 205-2)*(205 : ℝ)^2+(8*rankSymmetric256Parameter 205-5)*205-2) * rankSymmetric256IntegralWeight (205-1) +
      2 * rankSymmetric256RootAllowance 205 * (205 : ℝ) ≤ rankSymmetric256Coercivity 205 * (205 : ℝ)^2 * rankSymmetric256IntegralWeight 205) ∧
    (((2*(205 : ℝ)^2+3*205-2) * rankSymmetric256IntegralWeight (205-1) +
      2 * rankSymmetric256RootAllowance 205 * (205 : ℝ) ≤ (205 : ℝ)^2 * rankSymmetric256CumulantWeight 205)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset205, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_206 :
    (rankSymmetric256IntegralWeight (206-1) * rankSymmetric256Convolution 206 ≤ (rankSymmetric256RootAllowance 206)^2) ∧
    (((4*rankSymmetric256Parameter 206-2)*(206 : ℝ)^2+(8*rankSymmetric256Parameter 206-5)*206-2) * rankSymmetric256IntegralWeight (206-1) +
      2 * rankSymmetric256RootAllowance 206 * (206 : ℝ) ≤ rankSymmetric256Coercivity 206 * (206 : ℝ)^2 * rankSymmetric256IntegralWeight 206) ∧
    (((2*(206 : ℝ)^2+3*206-2) * rankSymmetric256IntegralWeight (206-1) +
      2 * rankSymmetric256RootAllowance 206 * (206 : ℝ) ≤ (206 : ℝ)^2 * rankSymmetric256CumulantWeight 206)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset206, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_207 :
    (rankSymmetric256IntegralWeight (207-1) * rankSymmetric256Convolution 207 ≤ (rankSymmetric256RootAllowance 207)^2) ∧
    (((4*rankSymmetric256Parameter 207-2)*(207 : ℝ)^2+(8*rankSymmetric256Parameter 207-5)*207-2) * rankSymmetric256IntegralWeight (207-1) +
      2 * rankSymmetric256RootAllowance 207 * (207 : ℝ) ≤ rankSymmetric256Coercivity 207 * (207 : ℝ)^2 * rankSymmetric256IntegralWeight 207) ∧
    (((2*(207 : ℝ)^2+3*207-2) * rankSymmetric256IntegralWeight (207-1) +
      2 * rankSymmetric256RootAllowance 207 * (207 : ℝ) ≤ (207 : ℝ)^2 * rankSymmetric256CumulantWeight 207)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset207, Finset.sum_Icc_succ_top]

theorem rankSymmetric256Certificate_208 :
    (rankSymmetric256IntegralWeight (208-1) * rankSymmetric256Convolution 208 ≤ (rankSymmetric256RootAllowance 208)^2) ∧
    (((4*rankSymmetric256Parameter 208-2)*(208 : ℝ)^2+(8*rankSymmetric256Parameter 208-5)*208-2) * rankSymmetric256IntegralWeight (208-1) +
      2 * rankSymmetric256RootAllowance 208 * (208 : ℝ) ≤ rankSymmetric256Coercivity 208 * (208 : ℝ)^2 * rankSymmetric256IntegralWeight 208) ∧
    (((2*(208 : ℝ)^2+3*208-2) * rankSymmetric256IntegralWeight (208-1) +
      2 * rankSymmetric256RootAllowance 208 * (208 : ℝ) ≤ (208 : ℝ)^2 * rankSymmetric256CumulantWeight 208)) := by
  norm_num [rankSymmetric256Coercivity, rankSymmetric256Convolution, rankSymmetric256CauchyWeight,
    rankSymmetric256CauchyOffset, rankSymmetric256CauchyOffset208, Finset.sum_Icc_succ_top]

end KLS.RouteArithmetic
end

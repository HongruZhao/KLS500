import OptTwentyEightHalfWeights

/-! Individual exact rational certificates keep kernel replay bounded. -/
set_option maxHeartbeats 8000000
noncomputable section
namespace KLS.RouteArithmetic

theorem twentyEightHalfFiniteCertificate_13 :
    ((40033/6000 : ℝ) * twentyEightHalfIntegralWeight (13-1) * ((13-2 : ℕ) : ℝ) *
      twentyEightHalfRankConvolution 13 ≤ (twentyEightHalfRootAllowance 13)^2) ∧
    ((7/3 : ℝ) * (((13+2 : ℕ) : ℝ) + 2*(13 : ℝ)*(5*(13 : ℝ)-2)) * twentyEightHalfIntegralWeight (13-1) +
      2 * twentyEightHalfRootAllowance 13 * (13 : ℝ) ≤
        (57/2 : ℝ) * (13 : ℝ)^2 * twentyEightHalfIntegralWeight 13) := by
  norm_num [twentyEightHalfIntegralWeight, twentyEightHalfCumulantWeight,
    twentyEightHalfRankConvolution, twentyEightHalfRootAllowance, Finset.sum_Icc_succ_top]

theorem twentyEightHalfFiniteCertificate_14 :
    ((40033/6000 : ℝ) * twentyEightHalfIntegralWeight (14-1) * ((14-2 : ℕ) : ℝ) *
      twentyEightHalfRankConvolution 14 ≤ (twentyEightHalfRootAllowance 14)^2) ∧
    ((7/3 : ℝ) * (((14+2 : ℕ) : ℝ) + 2*(14 : ℝ)*(5*(14 : ℝ)-2)) * twentyEightHalfIntegralWeight (14-1) +
      2 * twentyEightHalfRootAllowance 14 * (14 : ℝ) ≤
        (57/2 : ℝ) * (14 : ℝ)^2 * twentyEightHalfIntegralWeight 14) := by
  norm_num [twentyEightHalfIntegralWeight, twentyEightHalfCumulantWeight,
    twentyEightHalfRankConvolution, twentyEightHalfRootAllowance, Finset.sum_Icc_succ_top]

theorem twentyEightHalfFiniteCertificate_15 :
    ((40033/6000 : ℝ) * twentyEightHalfIntegralWeight (15-1) * ((15-2 : ℕ) : ℝ) *
      twentyEightHalfRankConvolution 15 ≤ (twentyEightHalfRootAllowance 15)^2) ∧
    ((7/3 : ℝ) * (((15+2 : ℕ) : ℝ) + 2*(15 : ℝ)*(5*(15 : ℝ)-2)) * twentyEightHalfIntegralWeight (15-1) +
      2 * twentyEightHalfRootAllowance 15 * (15 : ℝ) ≤
        (57/2 : ℝ) * (15 : ℝ)^2 * twentyEightHalfIntegralWeight 15) := by
  norm_num [twentyEightHalfIntegralWeight, twentyEightHalfCumulantWeight,
    twentyEightHalfRankConvolution, twentyEightHalfRootAllowance, Finset.sum_Icc_succ_top]

theorem twentyEightHalfFiniteCertificate_16 :
    ((40033/6000 : ℝ) * twentyEightHalfIntegralWeight (16-1) * ((16-2 : ℕ) : ℝ) *
      twentyEightHalfRankConvolution 16 ≤ (twentyEightHalfRootAllowance 16)^2) ∧
    ((7/3 : ℝ) * (((16+2 : ℕ) : ℝ) + 2*(16 : ℝ)*(5*(16 : ℝ)-2)) * twentyEightHalfIntegralWeight (16-1) +
      2 * twentyEightHalfRootAllowance 16 * (16 : ℝ) ≤
        (57/2 : ℝ) * (16 : ℝ)^2 * twentyEightHalfIntegralWeight 16) := by
  norm_num [twentyEightHalfIntegralWeight, twentyEightHalfCumulantWeight,
    twentyEightHalfRankConvolution, twentyEightHalfRootAllowance, Finset.sum_Icc_succ_top]

theorem twentyEightHalfFiniteCertificate_17 :
    ((40033/6000 : ℝ) * twentyEightHalfIntegralWeight (17-1) * ((17-2 : ℕ) : ℝ) *
      twentyEightHalfRankConvolution 17 ≤ (twentyEightHalfRootAllowance 17)^2) ∧
    ((7/3 : ℝ) * (((17+2 : ℕ) : ℝ) + 2*(17 : ℝ)*(5*(17 : ℝ)-2)) * twentyEightHalfIntegralWeight (17-1) +
      2 * twentyEightHalfRootAllowance 17 * (17 : ℝ) ≤
        (57/2 : ℝ) * (17 : ℝ)^2 * twentyEightHalfIntegralWeight 17) := by
  norm_num [twentyEightHalfIntegralWeight, twentyEightHalfCumulantWeight,
    twentyEightHalfRankConvolution, twentyEightHalfRootAllowance, Finset.sum_Icc_succ_top]

theorem twentyEightHalfFiniteCertificate_18 :
    ((40033/6000 : ℝ) * twentyEightHalfIntegralWeight (18-1) * ((18-2 : ℕ) : ℝ) *
      twentyEightHalfRankConvolution 18 ≤ (twentyEightHalfRootAllowance 18)^2) ∧
    ((7/3 : ℝ) * (((18+2 : ℕ) : ℝ) + 2*(18 : ℝ)*(5*(18 : ℝ)-2)) * twentyEightHalfIntegralWeight (18-1) +
      2 * twentyEightHalfRootAllowance 18 * (18 : ℝ) ≤
        (57/2 : ℝ) * (18 : ℝ)^2 * twentyEightHalfIntegralWeight 18) := by
  norm_num [twentyEightHalfIntegralWeight, twentyEightHalfCumulantWeight,
    twentyEightHalfRankConvolution, twentyEightHalfRootAllowance, Finset.sum_Icc_succ_top]

theorem twentyEightHalfFiniteCertificate_19 :
    ((40033/6000 : ℝ) * twentyEightHalfIntegralWeight (19-1) * ((19-2 : ℕ) : ℝ) *
      twentyEightHalfRankConvolution 19 ≤ (twentyEightHalfRootAllowance 19)^2) ∧
    ((7/3 : ℝ) * (((19+2 : ℕ) : ℝ) + 2*(19 : ℝ)*(5*(19 : ℝ)-2)) * twentyEightHalfIntegralWeight (19-1) +
      2 * twentyEightHalfRootAllowance 19 * (19 : ℝ) ≤
        (57/2 : ℝ) * (19 : ℝ)^2 * twentyEightHalfIntegralWeight 19) := by
  norm_num [twentyEightHalfIntegralWeight, twentyEightHalfCumulantWeight,
    twentyEightHalfRankConvolution, twentyEightHalfRootAllowance, Finset.sum_Icc_succ_top]

theorem twentyEightHalfFiniteCertificate_20 :
    ((40033/6000 : ℝ) * twentyEightHalfIntegralWeight (20-1) * ((20-2 : ℕ) : ℝ) *
      twentyEightHalfRankConvolution 20 ≤ (twentyEightHalfRootAllowance 20)^2) ∧
    ((7/3 : ℝ) * (((20+2 : ℕ) : ℝ) + 2*(20 : ℝ)*(5*(20 : ℝ)-2)) * twentyEightHalfIntegralWeight (20-1) +
      2 * twentyEightHalfRootAllowance 20 * (20 : ℝ) ≤
        (57/2 : ℝ) * (20 : ℝ)^2 * twentyEightHalfIntegralWeight 20) := by
  norm_num [twentyEightHalfIntegralWeight, twentyEightHalfCumulantWeight,
    twentyEightHalfRankConvolution, twentyEightHalfRootAllowance, Finset.sum_Icc_succ_top]

theorem twentyEightHalfFiniteCertificate_21 :
    ((40033/6000 : ℝ) * twentyEightHalfIntegralWeight (21-1) * ((21-2 : ℕ) : ℝ) *
      twentyEightHalfRankConvolution 21 ≤ (twentyEightHalfRootAllowance 21)^2) ∧
    ((7/3 : ℝ) * (((21+2 : ℕ) : ℝ) + 2*(21 : ℝ)*(5*(21 : ℝ)-2)) * twentyEightHalfIntegralWeight (21-1) +
      2 * twentyEightHalfRootAllowance 21 * (21 : ℝ) ≤
        (57/2 : ℝ) * (21 : ℝ)^2 * twentyEightHalfIntegralWeight 21) := by
  norm_num [twentyEightHalfIntegralWeight, twentyEightHalfCumulantWeight,
    twentyEightHalfRankConvolution, twentyEightHalfRootAllowance, Finset.sum_Icc_succ_top]

theorem twentyEightHalfFiniteCertificate_22 :
    ((40033/6000 : ℝ) * twentyEightHalfIntegralWeight (22-1) * ((22-2 : ℕ) : ℝ) *
      twentyEightHalfRankConvolution 22 ≤ (twentyEightHalfRootAllowance 22)^2) ∧
    ((7/3 : ℝ) * (((22+2 : ℕ) : ℝ) + 2*(22 : ℝ)*(5*(22 : ℝ)-2)) * twentyEightHalfIntegralWeight (22-1) +
      2 * twentyEightHalfRootAllowance 22 * (22 : ℝ) ≤
        (57/2 : ℝ) * (22 : ℝ)^2 * twentyEightHalfIntegralWeight 22) := by
  norm_num [twentyEightHalfIntegralWeight, twentyEightHalfCumulantWeight,
    twentyEightHalfRankConvolution, twentyEightHalfRootAllowance, Finset.sum_Icc_succ_top]

theorem twentyEightHalfFiniteCertificate_23 :
    ((40033/6000 : ℝ) * twentyEightHalfIntegralWeight (23-1) * ((23-2 : ℕ) : ℝ) *
      twentyEightHalfRankConvolution 23 ≤ (twentyEightHalfRootAllowance 23)^2) ∧
    ((7/3 : ℝ) * (((23+2 : ℕ) : ℝ) + 2*(23 : ℝ)*(5*(23 : ℝ)-2)) * twentyEightHalfIntegralWeight (23-1) +
      2 * twentyEightHalfRootAllowance 23 * (23 : ℝ) ≤
        (57/2 : ℝ) * (23 : ℝ)^2 * twentyEightHalfIntegralWeight 23) := by
  norm_num [twentyEightHalfIntegralWeight, twentyEightHalfCumulantWeight,
    twentyEightHalfRankConvolution, twentyEightHalfRootAllowance, Finset.sum_Icc_succ_top]

end KLS.RouteArithmetic
end

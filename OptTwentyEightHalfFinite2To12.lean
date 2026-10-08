import OptTwentyEightHalfWeights

/-! Individual exact rational certificates keep kernel replay bounded. -/
set_option maxHeartbeats 8000000
noncomputable section
namespace KLS.RouteArithmetic

theorem twentyEightHalfFiniteCertificate_2 :
    ((40033/6000 : ℝ) * twentyEightHalfIntegralWeight (2-1) * ((2-2 : ℕ) : ℝ) *
      twentyEightHalfRankConvolution 2 ≤ (twentyEightHalfRootAllowance 2)^2) ∧
    ((7/3 : ℝ) * (((2+2 : ℕ) : ℝ) + 2*(2 : ℝ)*(5*(2 : ℝ)-2)) * twentyEightHalfIntegralWeight (2-1) +
      2 * twentyEightHalfRootAllowance 2 * (2 : ℝ) ≤
        (57/2 : ℝ) * (2 : ℝ)^2 * twentyEightHalfIntegralWeight 2) := by
  norm_num [twentyEightHalfIntegralWeight, twentyEightHalfCumulantWeight,
    twentyEightHalfRankConvolution, twentyEightHalfRootAllowance, Finset.sum_Icc_succ_top]

theorem twentyEightHalfFiniteCertificate_3 :
    ((40033/6000 : ℝ) * twentyEightHalfIntegralWeight (3-1) * ((3-2 : ℕ) : ℝ) *
      twentyEightHalfRankConvolution 3 ≤ (twentyEightHalfRootAllowance 3)^2) ∧
    ((7/3 : ℝ) * (((3+2 : ℕ) : ℝ) + 2*(3 : ℝ)*(5*(3 : ℝ)-2)) * twentyEightHalfIntegralWeight (3-1) +
      2 * twentyEightHalfRootAllowance 3 * (3 : ℝ) ≤
        (57/2 : ℝ) * (3 : ℝ)^2 * twentyEightHalfIntegralWeight 3) := by
  norm_num [twentyEightHalfIntegralWeight, twentyEightHalfCumulantWeight,
    twentyEightHalfRankConvolution, twentyEightHalfRootAllowance, Finset.sum_Icc_succ_top]

theorem twentyEightHalfFiniteCertificate_4 :
    ((40033/6000 : ℝ) * twentyEightHalfIntegralWeight (4-1) * ((4-2 : ℕ) : ℝ) *
      twentyEightHalfRankConvolution 4 ≤ (twentyEightHalfRootAllowance 4)^2) ∧
    ((7/3 : ℝ) * (((4+2 : ℕ) : ℝ) + 2*(4 : ℝ)*(5*(4 : ℝ)-2)) * twentyEightHalfIntegralWeight (4-1) +
      2 * twentyEightHalfRootAllowance 4 * (4 : ℝ) ≤
        (57/2 : ℝ) * (4 : ℝ)^2 * twentyEightHalfIntegralWeight 4) := by
  norm_num [twentyEightHalfIntegralWeight, twentyEightHalfCumulantWeight,
    twentyEightHalfRankConvolution, twentyEightHalfRootAllowance, Finset.sum_Icc_succ_top]

theorem twentyEightHalfFiniteCertificate_5 :
    ((40033/6000 : ℝ) * twentyEightHalfIntegralWeight (5-1) * ((5-2 : ℕ) : ℝ) *
      twentyEightHalfRankConvolution 5 ≤ (twentyEightHalfRootAllowance 5)^2) ∧
    ((7/3 : ℝ) * (((5+2 : ℕ) : ℝ) + 2*(5 : ℝ)*(5*(5 : ℝ)-2)) * twentyEightHalfIntegralWeight (5-1) +
      2 * twentyEightHalfRootAllowance 5 * (5 : ℝ) ≤
        (57/2 : ℝ) * (5 : ℝ)^2 * twentyEightHalfIntegralWeight 5) := by
  norm_num [twentyEightHalfIntegralWeight, twentyEightHalfCumulantWeight,
    twentyEightHalfRankConvolution, twentyEightHalfRootAllowance, Finset.sum_Icc_succ_top]

theorem twentyEightHalfFiniteCertificate_6 :
    ((40033/6000 : ℝ) * twentyEightHalfIntegralWeight (6-1) * ((6-2 : ℕ) : ℝ) *
      twentyEightHalfRankConvolution 6 ≤ (twentyEightHalfRootAllowance 6)^2) ∧
    ((7/3 : ℝ) * (((6+2 : ℕ) : ℝ) + 2*(6 : ℝ)*(5*(6 : ℝ)-2)) * twentyEightHalfIntegralWeight (6-1) +
      2 * twentyEightHalfRootAllowance 6 * (6 : ℝ) ≤
        (57/2 : ℝ) * (6 : ℝ)^2 * twentyEightHalfIntegralWeight 6) := by
  norm_num [twentyEightHalfIntegralWeight, twentyEightHalfCumulantWeight,
    twentyEightHalfRankConvolution, twentyEightHalfRootAllowance, Finset.sum_Icc_succ_top]

theorem twentyEightHalfFiniteCertificate_7 :
    ((40033/6000 : ℝ) * twentyEightHalfIntegralWeight (7-1) * ((7-2 : ℕ) : ℝ) *
      twentyEightHalfRankConvolution 7 ≤ (twentyEightHalfRootAllowance 7)^2) ∧
    ((7/3 : ℝ) * (((7+2 : ℕ) : ℝ) + 2*(7 : ℝ)*(5*(7 : ℝ)-2)) * twentyEightHalfIntegralWeight (7-1) +
      2 * twentyEightHalfRootAllowance 7 * (7 : ℝ) ≤
        (57/2 : ℝ) * (7 : ℝ)^2 * twentyEightHalfIntegralWeight 7) := by
  norm_num [twentyEightHalfIntegralWeight, twentyEightHalfCumulantWeight,
    twentyEightHalfRankConvolution, twentyEightHalfRootAllowance, Finset.sum_Icc_succ_top]

theorem twentyEightHalfFiniteCertificate_8 :
    ((40033/6000 : ℝ) * twentyEightHalfIntegralWeight (8-1) * ((8-2 : ℕ) : ℝ) *
      twentyEightHalfRankConvolution 8 ≤ (twentyEightHalfRootAllowance 8)^2) ∧
    ((7/3 : ℝ) * (((8+2 : ℕ) : ℝ) + 2*(8 : ℝ)*(5*(8 : ℝ)-2)) * twentyEightHalfIntegralWeight (8-1) +
      2 * twentyEightHalfRootAllowance 8 * (8 : ℝ) ≤
        (57/2 : ℝ) * (8 : ℝ)^2 * twentyEightHalfIntegralWeight 8) := by
  norm_num [twentyEightHalfIntegralWeight, twentyEightHalfCumulantWeight,
    twentyEightHalfRankConvolution, twentyEightHalfRootAllowance, Finset.sum_Icc_succ_top]

theorem twentyEightHalfFiniteCertificate_9 :
    ((40033/6000 : ℝ) * twentyEightHalfIntegralWeight (9-1) * ((9-2 : ℕ) : ℝ) *
      twentyEightHalfRankConvolution 9 ≤ (twentyEightHalfRootAllowance 9)^2) ∧
    ((7/3 : ℝ) * (((9+2 : ℕ) : ℝ) + 2*(9 : ℝ)*(5*(9 : ℝ)-2)) * twentyEightHalfIntegralWeight (9-1) +
      2 * twentyEightHalfRootAllowance 9 * (9 : ℝ) ≤
        (57/2 : ℝ) * (9 : ℝ)^2 * twentyEightHalfIntegralWeight 9) := by
  norm_num [twentyEightHalfIntegralWeight, twentyEightHalfCumulantWeight,
    twentyEightHalfRankConvolution, twentyEightHalfRootAllowance, Finset.sum_Icc_succ_top]

theorem twentyEightHalfFiniteCertificate_10 :
    ((40033/6000 : ℝ) * twentyEightHalfIntegralWeight (10-1) * ((10-2 : ℕ) : ℝ) *
      twentyEightHalfRankConvolution 10 ≤ (twentyEightHalfRootAllowance 10)^2) ∧
    ((7/3 : ℝ) * (((10+2 : ℕ) : ℝ) + 2*(10 : ℝ)*(5*(10 : ℝ)-2)) * twentyEightHalfIntegralWeight (10-1) +
      2 * twentyEightHalfRootAllowance 10 * (10 : ℝ) ≤
        (57/2 : ℝ) * (10 : ℝ)^2 * twentyEightHalfIntegralWeight 10) := by
  norm_num [twentyEightHalfIntegralWeight, twentyEightHalfCumulantWeight,
    twentyEightHalfRankConvolution, twentyEightHalfRootAllowance, Finset.sum_Icc_succ_top]

theorem twentyEightHalfFiniteCertificate_11 :
    ((40033/6000 : ℝ) * twentyEightHalfIntegralWeight (11-1) * ((11-2 : ℕ) : ℝ) *
      twentyEightHalfRankConvolution 11 ≤ (twentyEightHalfRootAllowance 11)^2) ∧
    ((7/3 : ℝ) * (((11+2 : ℕ) : ℝ) + 2*(11 : ℝ)*(5*(11 : ℝ)-2)) * twentyEightHalfIntegralWeight (11-1) +
      2 * twentyEightHalfRootAllowance 11 * (11 : ℝ) ≤
        (57/2 : ℝ) * (11 : ℝ)^2 * twentyEightHalfIntegralWeight 11) := by
  norm_num [twentyEightHalfIntegralWeight, twentyEightHalfCumulantWeight,
    twentyEightHalfRankConvolution, twentyEightHalfRootAllowance, Finset.sum_Icc_succ_top]

theorem twentyEightHalfFiniteCertificate_12 :
    ((40033/6000 : ℝ) * twentyEightHalfIntegralWeight (12-1) * ((12-2 : ℕ) : ℝ) *
      twentyEightHalfRankConvolution 12 ≤ (twentyEightHalfRootAllowance 12)^2) ∧
    ((7/3 : ℝ) * (((12+2 : ℕ) : ℝ) + 2*(12 : ℝ)*(5*(12 : ℝ)-2)) * twentyEightHalfIntegralWeight (12-1) +
      2 * twentyEightHalfRootAllowance 12 * (12 : ℝ) ≤
        (57/2 : ℝ) * (12 : ℝ)^2 * twentyEightHalfIntegralWeight 12) := by
  norm_num [twentyEightHalfIntegralWeight, twentyEightHalfCumulantWeight,
    twentyEightHalfRankConvolution, twentyEightHalfRootAllowance, Finset.sum_Icc_succ_top]

end KLS.RouteArithmetic
end

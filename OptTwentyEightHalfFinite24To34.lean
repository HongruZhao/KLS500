import OptTwentyEightHalfWeights

/-! Individual exact rational certificates keep kernel replay bounded. -/
set_option maxHeartbeats 8000000
noncomputable section
namespace KLS.RouteArithmetic

theorem twentyEightHalfFiniteCertificate_24 :
    ((40033/6000 : ℝ) * twentyEightHalfIntegralWeight (24-1) * ((24-2 : ℕ) : ℝ) *
      twentyEightHalfRankConvolution 24 ≤ (twentyEightHalfRootAllowance 24)^2) ∧
    ((7/3 : ℝ) * (((24+2 : ℕ) : ℝ) + 2*(24 : ℝ)*(5*(24 : ℝ)-2)) * twentyEightHalfIntegralWeight (24-1) +
      2 * twentyEightHalfRootAllowance 24 * (24 : ℝ) ≤
        (57/2 : ℝ) * (24 : ℝ)^2 * twentyEightHalfIntegralWeight 24) := by
  norm_num [twentyEightHalfIntegralWeight, twentyEightHalfCumulantWeight,
    twentyEightHalfRankConvolution, twentyEightHalfRootAllowance, Finset.sum_Icc_succ_top]

theorem twentyEightHalfFiniteCertificate_25 :
    ((40033/6000 : ℝ) * twentyEightHalfIntegralWeight (25-1) * ((25-2 : ℕ) : ℝ) *
      twentyEightHalfRankConvolution 25 ≤ (twentyEightHalfRootAllowance 25)^2) ∧
    ((7/3 : ℝ) * (((25+2 : ℕ) : ℝ) + 2*(25 : ℝ)*(5*(25 : ℝ)-2)) * twentyEightHalfIntegralWeight (25-1) +
      2 * twentyEightHalfRootAllowance 25 * (25 : ℝ) ≤
        (57/2 : ℝ) * (25 : ℝ)^2 * twentyEightHalfIntegralWeight 25) := by
  norm_num [twentyEightHalfIntegralWeight, twentyEightHalfCumulantWeight,
    twentyEightHalfRankConvolution, twentyEightHalfRootAllowance, Finset.sum_Icc_succ_top]

theorem twentyEightHalfFiniteCertificate_26 :
    ((40033/6000 : ℝ) * twentyEightHalfIntegralWeight (26-1) * ((26-2 : ℕ) : ℝ) *
      twentyEightHalfRankConvolution 26 ≤ (twentyEightHalfRootAllowance 26)^2) ∧
    ((7/3 : ℝ) * (((26+2 : ℕ) : ℝ) + 2*(26 : ℝ)*(5*(26 : ℝ)-2)) * twentyEightHalfIntegralWeight (26-1) +
      2 * twentyEightHalfRootAllowance 26 * (26 : ℝ) ≤
        (57/2 : ℝ) * (26 : ℝ)^2 * twentyEightHalfIntegralWeight 26) := by
  norm_num [twentyEightHalfIntegralWeight, twentyEightHalfCumulantWeight,
    twentyEightHalfRankConvolution, twentyEightHalfRootAllowance, Finset.sum_Icc_succ_top]

theorem twentyEightHalfFiniteCertificate_27 :
    ((40033/6000 : ℝ) * twentyEightHalfIntegralWeight (27-1) * ((27-2 : ℕ) : ℝ) *
      twentyEightHalfRankConvolution 27 ≤ (twentyEightHalfRootAllowance 27)^2) ∧
    ((7/3 : ℝ) * (((27+2 : ℕ) : ℝ) + 2*(27 : ℝ)*(5*(27 : ℝ)-2)) * twentyEightHalfIntegralWeight (27-1) +
      2 * twentyEightHalfRootAllowance 27 * (27 : ℝ) ≤
        (57/2 : ℝ) * (27 : ℝ)^2 * twentyEightHalfIntegralWeight 27) := by
  norm_num [twentyEightHalfIntegralWeight, twentyEightHalfCumulantWeight,
    twentyEightHalfRankConvolution, twentyEightHalfRootAllowance, Finset.sum_Icc_succ_top]

theorem twentyEightHalfFiniteCertificate_28 :
    ((40033/6000 : ℝ) * twentyEightHalfIntegralWeight (28-1) * ((28-2 : ℕ) : ℝ) *
      twentyEightHalfRankConvolution 28 ≤ (twentyEightHalfRootAllowance 28)^2) ∧
    ((7/3 : ℝ) * (((28+2 : ℕ) : ℝ) + 2*(28 : ℝ)*(5*(28 : ℝ)-2)) * twentyEightHalfIntegralWeight (28-1) +
      2 * twentyEightHalfRootAllowance 28 * (28 : ℝ) ≤
        (57/2 : ℝ) * (28 : ℝ)^2 * twentyEightHalfIntegralWeight 28) := by
  norm_num [twentyEightHalfIntegralWeight, twentyEightHalfCumulantWeight,
    twentyEightHalfRankConvolution, twentyEightHalfRootAllowance, Finset.sum_Icc_succ_top]

theorem twentyEightHalfFiniteCertificate_29 :
    ((40033/6000 : ℝ) * twentyEightHalfIntegralWeight (29-1) * ((29-2 : ℕ) : ℝ) *
      twentyEightHalfRankConvolution 29 ≤ (twentyEightHalfRootAllowance 29)^2) ∧
    ((7/3 : ℝ) * (((29+2 : ℕ) : ℝ) + 2*(29 : ℝ)*(5*(29 : ℝ)-2)) * twentyEightHalfIntegralWeight (29-1) +
      2 * twentyEightHalfRootAllowance 29 * (29 : ℝ) ≤
        (57/2 : ℝ) * (29 : ℝ)^2 * twentyEightHalfIntegralWeight 29) := by
  norm_num [twentyEightHalfIntegralWeight, twentyEightHalfCumulantWeight,
    twentyEightHalfRankConvolution, twentyEightHalfRootAllowance, Finset.sum_Icc_succ_top]

theorem twentyEightHalfFiniteCertificate_30 :
    ((40033/6000 : ℝ) * twentyEightHalfIntegralWeight (30-1) * ((30-2 : ℕ) : ℝ) *
      twentyEightHalfRankConvolution 30 ≤ (twentyEightHalfRootAllowance 30)^2) ∧
    ((7/3 : ℝ) * (((30+2 : ℕ) : ℝ) + 2*(30 : ℝ)*(5*(30 : ℝ)-2)) * twentyEightHalfIntegralWeight (30-1) +
      2 * twentyEightHalfRootAllowance 30 * (30 : ℝ) ≤
        (57/2 : ℝ) * (30 : ℝ)^2 * twentyEightHalfIntegralWeight 30) := by
  norm_num [twentyEightHalfIntegralWeight, twentyEightHalfCumulantWeight,
    twentyEightHalfRankConvolution, twentyEightHalfRootAllowance, Finset.sum_Icc_succ_top]

theorem twentyEightHalfFiniteCertificate_31 :
    ((40033/6000 : ℝ) * twentyEightHalfIntegralWeight (31-1) * ((31-2 : ℕ) : ℝ) *
      twentyEightHalfRankConvolution 31 ≤ (twentyEightHalfRootAllowance 31)^2) ∧
    ((7/3 : ℝ) * (((31+2 : ℕ) : ℝ) + 2*(31 : ℝ)*(5*(31 : ℝ)-2)) * twentyEightHalfIntegralWeight (31-1) +
      2 * twentyEightHalfRootAllowance 31 * (31 : ℝ) ≤
        (57/2 : ℝ) * (31 : ℝ)^2 * twentyEightHalfIntegralWeight 31) := by
  norm_num [twentyEightHalfIntegralWeight, twentyEightHalfCumulantWeight,
    twentyEightHalfRankConvolution, twentyEightHalfRootAllowance, Finset.sum_Icc_succ_top]

theorem twentyEightHalfFiniteCertificate_32 :
    ((40033/6000 : ℝ) * twentyEightHalfIntegralWeight (32-1) * ((32-2 : ℕ) : ℝ) *
      twentyEightHalfRankConvolution 32 ≤ (twentyEightHalfRootAllowance 32)^2) ∧
    ((7/3 : ℝ) * (((32+2 : ℕ) : ℝ) + 2*(32 : ℝ)*(5*(32 : ℝ)-2)) * twentyEightHalfIntegralWeight (32-1) +
      2 * twentyEightHalfRootAllowance 32 * (32 : ℝ) ≤
        (57/2 : ℝ) * (32 : ℝ)^2 * twentyEightHalfIntegralWeight 32) := by
  norm_num [twentyEightHalfIntegralWeight, twentyEightHalfCumulantWeight,
    twentyEightHalfRankConvolution, twentyEightHalfRootAllowance, Finset.sum_Icc_succ_top]

theorem twentyEightHalfFiniteCertificate_33 :
    ((40033/6000 : ℝ) * twentyEightHalfIntegralWeight (33-1) * ((33-2 : ℕ) : ℝ) *
      twentyEightHalfRankConvolution 33 ≤ (twentyEightHalfRootAllowance 33)^2) ∧
    ((7/3 : ℝ) * (((33+2 : ℕ) : ℝ) + 2*(33 : ℝ)*(5*(33 : ℝ)-2)) * twentyEightHalfIntegralWeight (33-1) +
      2 * twentyEightHalfRootAllowance 33 * (33 : ℝ) ≤
        (57/2 : ℝ) * (33 : ℝ)^2 * twentyEightHalfIntegralWeight 33) := by
  norm_num [twentyEightHalfIntegralWeight, twentyEightHalfCumulantWeight,
    twentyEightHalfRankConvolution, twentyEightHalfRootAllowance, Finset.sum_Icc_succ_top]

theorem twentyEightHalfFiniteCertificate_34 :
    ((40033/6000 : ℝ) * twentyEightHalfIntegralWeight (34-1) * ((34-2 : ℕ) : ℝ) *
      twentyEightHalfRankConvolution 34 ≤ (twentyEightHalfRootAllowance 34)^2) ∧
    ((7/3 : ℝ) * (((34+2 : ℕ) : ℝ) + 2*(34 : ℝ)*(5*(34 : ℝ)-2)) * twentyEightHalfIntegralWeight (34-1) +
      2 * twentyEightHalfRootAllowance 34 * (34 : ℝ) ≤
        (57/2 : ℝ) * (34 : ℝ)^2 * twentyEightHalfIntegralWeight 34) := by
  norm_num [twentyEightHalfIntegralWeight, twentyEightHalfCumulantWeight,
    twentyEightHalfRankConvolution, twentyEightHalfRootAllowance, Finset.sum_Icc_succ_top]

end KLS.RouteArithmetic
end

import OptRankCauchyWeights

/-! Exact finite-rank arithmetic certificates, with no floating-point
or native evaluation in the proof terms. -/
set_option maxHeartbeats 2000000
noncomputable section
namespace KLS.RouteArithmetic

theorem rankCauchyCertificate_2 :
    (rankCauchyIntegralWeight (2-1) * rankCauchyConvolution 2 ≤
      (rankCauchyRootAllowance 2)^2) ∧
    (((( 2+2 : ℕ) : ℝ) + 2*(2 : ℝ)*(5*(2 : ℝ)-2)) * rankCauchyIntegralWeight (2-1) +
      2 * rankCauchyRootAllowance 2 * (2 : ℝ) ≤
        (3/7 : ℝ) * (2 : ℝ)^2 * rankCauchyIntegralWeight 2) ∧
    (3 ≤ 2 →
      (((( 2+2 : ℕ) : ℝ) + 4*(2 : ℝ)*((2 : ℝ)-1)) * rankCauchyIntegralWeight (2-1) +
        2 * rankCauchyRootAllowance 2 * (2 : ℝ) ≤
          (2 : ℝ)^2 * rankCauchyCumulantWeight 2)) := by
  norm_num [rankCauchyConvolution, rankCauchyWeight, Finset.sum_Icc_succ_top]

theorem rankCauchyCertificate_3 :
    (rankCauchyIntegralWeight (3-1) * rankCauchyConvolution 3 ≤
      (rankCauchyRootAllowance 3)^2) ∧
    (((( 3+2 : ℕ) : ℝ) + 2*(3 : ℝ)*(5*(3 : ℝ)-2)) * rankCauchyIntegralWeight (3-1) +
      2 * rankCauchyRootAllowance 3 * (3 : ℝ) ≤
        (3/7 : ℝ) * (3 : ℝ)^2 * rankCauchyIntegralWeight 3) ∧
    (3 ≤ 3 →
      (((( 3+2 : ℕ) : ℝ) + 4*(3 : ℝ)*((3 : ℝ)-1)) * rankCauchyIntegralWeight (3-1) +
        2 * rankCauchyRootAllowance 3 * (3 : ℝ) ≤
          (3 : ℝ)^2 * rankCauchyCumulantWeight 3)) := by
  norm_num [rankCauchyConvolution, rankCauchyWeight, Finset.sum_Icc_succ_top]

theorem rankCauchyCertificate_4 :
    (rankCauchyIntegralWeight (4-1) * rankCauchyConvolution 4 ≤
      (rankCauchyRootAllowance 4)^2) ∧
    (((( 4+2 : ℕ) : ℝ) + 2*(4 : ℝ)*(5*(4 : ℝ)-2)) * rankCauchyIntegralWeight (4-1) +
      2 * rankCauchyRootAllowance 4 * (4 : ℝ) ≤
        (3/7 : ℝ) * (4 : ℝ)^2 * rankCauchyIntegralWeight 4) ∧
    (3 ≤ 4 →
      (((( 4+2 : ℕ) : ℝ) + 4*(4 : ℝ)*((4 : ℝ)-1)) * rankCauchyIntegralWeight (4-1) +
        2 * rankCauchyRootAllowance 4 * (4 : ℝ) ≤
          (4 : ℝ)^2 * rankCauchyCumulantWeight 4)) := by
  norm_num [rankCauchyConvolution, rankCauchyWeight, Finset.sum_Icc_succ_top]

theorem rankCauchyCertificate_5 :
    (rankCauchyIntegralWeight (5-1) * rankCauchyConvolution 5 ≤
      (rankCauchyRootAllowance 5)^2) ∧
    (((( 5+2 : ℕ) : ℝ) + 2*(5 : ℝ)*(5*(5 : ℝ)-2)) * rankCauchyIntegralWeight (5-1) +
      2 * rankCauchyRootAllowance 5 * (5 : ℝ) ≤
        (3/7 : ℝ) * (5 : ℝ)^2 * rankCauchyIntegralWeight 5) ∧
    (3 ≤ 5 →
      (((( 5+2 : ℕ) : ℝ) + 4*(5 : ℝ)*((5 : ℝ)-1)) * rankCauchyIntegralWeight (5-1) +
        2 * rankCauchyRootAllowance 5 * (5 : ℝ) ≤
          (5 : ℝ)^2 * rankCauchyCumulantWeight 5)) := by
  norm_num [rankCauchyConvolution, rankCauchyWeight, Finset.sum_Icc_succ_top]

theorem rankCauchyCertificate_6 :
    (rankCauchyIntegralWeight (6-1) * rankCauchyConvolution 6 ≤
      (rankCauchyRootAllowance 6)^2) ∧
    (((( 6+2 : ℕ) : ℝ) + 2*(6 : ℝ)*(5*(6 : ℝ)-2)) * rankCauchyIntegralWeight (6-1) +
      2 * rankCauchyRootAllowance 6 * (6 : ℝ) ≤
        (3/7 : ℝ) * (6 : ℝ)^2 * rankCauchyIntegralWeight 6) ∧
    (3 ≤ 6 →
      (((( 6+2 : ℕ) : ℝ) + 4*(6 : ℝ)*((6 : ℝ)-1)) * rankCauchyIntegralWeight (6-1) +
        2 * rankCauchyRootAllowance 6 * (6 : ℝ) ≤
          (6 : ℝ)^2 * rankCauchyCumulantWeight 6)) := by
  norm_num [rankCauchyConvolution, rankCauchyWeight, Finset.sum_Icc_succ_top]

theorem rankCauchyCertificate_7 :
    (rankCauchyIntegralWeight (7-1) * rankCauchyConvolution 7 ≤
      (rankCauchyRootAllowance 7)^2) ∧
    (((( 7+2 : ℕ) : ℝ) + 2*(7 : ℝ)*(5*(7 : ℝ)-2)) * rankCauchyIntegralWeight (7-1) +
      2 * rankCauchyRootAllowance 7 * (7 : ℝ) ≤
        (3/7 : ℝ) * (7 : ℝ)^2 * rankCauchyIntegralWeight 7) ∧
    (3 ≤ 7 →
      (((( 7+2 : ℕ) : ℝ) + 4*(7 : ℝ)*((7 : ℝ)-1)) * rankCauchyIntegralWeight (7-1) +
        2 * rankCauchyRootAllowance 7 * (7 : ℝ) ≤
          (7 : ℝ)^2 * rankCauchyCumulantWeight 7)) := by
  norm_num [rankCauchyConvolution, rankCauchyWeight, Finset.sum_Icc_succ_top]

theorem rankCauchyCertificate_8 :
    (rankCauchyIntegralWeight (8-1) * rankCauchyConvolution 8 ≤
      (rankCauchyRootAllowance 8)^2) ∧
    (((( 8+2 : ℕ) : ℝ) + 2*(8 : ℝ)*(5*(8 : ℝ)-2)) * rankCauchyIntegralWeight (8-1) +
      2 * rankCauchyRootAllowance 8 * (8 : ℝ) ≤
        (3/7 : ℝ) * (8 : ℝ)^2 * rankCauchyIntegralWeight 8) ∧
    (3 ≤ 8 →
      (((( 8+2 : ℕ) : ℝ) + 4*(8 : ℝ)*((8 : ℝ)-1)) * rankCauchyIntegralWeight (8-1) +
        2 * rankCauchyRootAllowance 8 * (8 : ℝ) ≤
          (8 : ℝ)^2 * rankCauchyCumulantWeight 8)) := by
  norm_num [rankCauchyConvolution, rankCauchyWeight, Finset.sum_Icc_succ_top]

theorem rankCauchyCertificate_9 :
    (rankCauchyIntegralWeight (9-1) * rankCauchyConvolution 9 ≤
      (rankCauchyRootAllowance 9)^2) ∧
    (((( 9+2 : ℕ) : ℝ) + 2*(9 : ℝ)*(5*(9 : ℝ)-2)) * rankCauchyIntegralWeight (9-1) +
      2 * rankCauchyRootAllowance 9 * (9 : ℝ) ≤
        (3/7 : ℝ) * (9 : ℝ)^2 * rankCauchyIntegralWeight 9) ∧
    (3 ≤ 9 →
      (((( 9+2 : ℕ) : ℝ) + 4*(9 : ℝ)*((9 : ℝ)-1)) * rankCauchyIntegralWeight (9-1) +
        2 * rankCauchyRootAllowance 9 * (9 : ℝ) ≤
          (9 : ℝ)^2 * rankCauchyCumulantWeight 9)) := by
  norm_num [rankCauchyConvolution, rankCauchyWeight, Finset.sum_Icc_succ_top]

theorem rankCauchyCertificate_10 :
    (rankCauchyIntegralWeight (10-1) * rankCauchyConvolution 10 ≤
      (rankCauchyRootAllowance 10)^2) ∧
    (((( 10+2 : ℕ) : ℝ) + 2*(10 : ℝ)*(5*(10 : ℝ)-2)) * rankCauchyIntegralWeight (10-1) +
      2 * rankCauchyRootAllowance 10 * (10 : ℝ) ≤
        (3/7 : ℝ) * (10 : ℝ)^2 * rankCauchyIntegralWeight 10) ∧
    (3 ≤ 10 →
      (((( 10+2 : ℕ) : ℝ) + 4*(10 : ℝ)*((10 : ℝ)-1)) * rankCauchyIntegralWeight (10-1) +
        2 * rankCauchyRootAllowance 10 * (10 : ℝ) ≤
          (10 : ℝ)^2 * rankCauchyCumulantWeight 10)) := by
  norm_num [rankCauchyConvolution, rankCauchyWeight, Finset.sum_Icc_succ_top]

theorem rankCauchyCertificate_11 :
    (rankCauchyIntegralWeight (11-1) * rankCauchyConvolution 11 ≤
      (rankCauchyRootAllowance 11)^2) ∧
    (((( 11+2 : ℕ) : ℝ) + 2*(11 : ℝ)*(5*(11 : ℝ)-2)) * rankCauchyIntegralWeight (11-1) +
      2 * rankCauchyRootAllowance 11 * (11 : ℝ) ≤
        (3/7 : ℝ) * (11 : ℝ)^2 * rankCauchyIntegralWeight 11) ∧
    (3 ≤ 11 →
      (((( 11+2 : ℕ) : ℝ) + 4*(11 : ℝ)*((11 : ℝ)-1)) * rankCauchyIntegralWeight (11-1) +
        2 * rankCauchyRootAllowance 11 * (11 : ℝ) ≤
          (11 : ℝ)^2 * rankCauchyCumulantWeight 11)) := by
  norm_num [rankCauchyConvolution, rankCauchyWeight, Finset.sum_Icc_succ_top]

theorem rankCauchyCertificate_12 :
    (rankCauchyIntegralWeight (12-1) * rankCauchyConvolution 12 ≤
      (rankCauchyRootAllowance 12)^2) ∧
    (((( 12+2 : ℕ) : ℝ) + 2*(12 : ℝ)*(5*(12 : ℝ)-2)) * rankCauchyIntegralWeight (12-1) +
      2 * rankCauchyRootAllowance 12 * (12 : ℝ) ≤
        (3/7 : ℝ) * (12 : ℝ)^2 * rankCauchyIntegralWeight 12) ∧
    (3 ≤ 12 →
      (((( 12+2 : ℕ) : ℝ) + 4*(12 : ℝ)*((12 : ℝ)-1)) * rankCauchyIntegralWeight (12-1) +
        2 * rankCauchyRootAllowance 12 * (12 : ℝ) ≤
          (12 : ℝ)^2 * rankCauchyCumulantWeight 12)) := by
  norm_num [rankCauchyConvolution, rankCauchyWeight, Finset.sum_Icc_succ_top]

theorem rankCauchyCertificate_13 :
    (rankCauchyIntegralWeight (13-1) * rankCauchyConvolution 13 ≤
      (rankCauchyRootAllowance 13)^2) ∧
    (((( 13+2 : ℕ) : ℝ) + 2*(13 : ℝ)*(5*(13 : ℝ)-2)) * rankCauchyIntegralWeight (13-1) +
      2 * rankCauchyRootAllowance 13 * (13 : ℝ) ≤
        (3/7 : ℝ) * (13 : ℝ)^2 * rankCauchyIntegralWeight 13) ∧
    (3 ≤ 13 →
      (((( 13+2 : ℕ) : ℝ) + 4*(13 : ℝ)*((13 : ℝ)-1)) * rankCauchyIntegralWeight (13-1) +
        2 * rankCauchyRootAllowance 13 * (13 : ℝ) ≤
          (13 : ℝ)^2 * rankCauchyCumulantWeight 13)) := by
  norm_num [rankCauchyConvolution, rankCauchyWeight, Finset.sum_Icc_succ_top]

theorem rankCauchyCertificate_14 :
    (rankCauchyIntegralWeight (14-1) * rankCauchyConvolution 14 ≤
      (rankCauchyRootAllowance 14)^2) ∧
    (((( 14+2 : ℕ) : ℝ) + 2*(14 : ℝ)*(5*(14 : ℝ)-2)) * rankCauchyIntegralWeight (14-1) +
      2 * rankCauchyRootAllowance 14 * (14 : ℝ) ≤
        (3/7 : ℝ) * (14 : ℝ)^2 * rankCauchyIntegralWeight 14) ∧
    (3 ≤ 14 →
      (((( 14+2 : ℕ) : ℝ) + 4*(14 : ℝ)*((14 : ℝ)-1)) * rankCauchyIntegralWeight (14-1) +
        2 * rankCauchyRootAllowance 14 * (14 : ℝ) ≤
          (14 : ℝ)^2 * rankCauchyCumulantWeight 14)) := by
  norm_num [rankCauchyConvolution, rankCauchyWeight, Finset.sum_Icc_succ_top]

theorem rankCauchyCertificate_15 :
    (rankCauchyIntegralWeight (15-1) * rankCauchyConvolution 15 ≤
      (rankCauchyRootAllowance 15)^2) ∧
    (((( 15+2 : ℕ) : ℝ) + 2*(15 : ℝ)*(5*(15 : ℝ)-2)) * rankCauchyIntegralWeight (15-1) +
      2 * rankCauchyRootAllowance 15 * (15 : ℝ) ≤
        (3/7 : ℝ) * (15 : ℝ)^2 * rankCauchyIntegralWeight 15) ∧
    (3 ≤ 15 →
      (((( 15+2 : ℕ) : ℝ) + 4*(15 : ℝ)*((15 : ℝ)-1)) * rankCauchyIntegralWeight (15-1) +
        2 * rankCauchyRootAllowance 15 * (15 : ℝ) ≤
          (15 : ℝ)^2 * rankCauchyCumulantWeight 15)) := by
  norm_num [rankCauchyConvolution, rankCauchyWeight, Finset.sum_Icc_succ_top]

theorem rankCauchyCertificate_16 :
    (rankCauchyIntegralWeight (16-1) * rankCauchyConvolution 16 ≤
      (rankCauchyRootAllowance 16)^2) ∧
    (((( 16+2 : ℕ) : ℝ) + 2*(16 : ℝ)*(5*(16 : ℝ)-2)) * rankCauchyIntegralWeight (16-1) +
      2 * rankCauchyRootAllowance 16 * (16 : ℝ) ≤
        (3/7 : ℝ) * (16 : ℝ)^2 * rankCauchyIntegralWeight 16) ∧
    (3 ≤ 16 →
      (((( 16+2 : ℕ) : ℝ) + 4*(16 : ℝ)*((16 : ℝ)-1)) * rankCauchyIntegralWeight (16-1) +
        2 * rankCauchyRootAllowance 16 * (16 : ℝ) ≤
          (16 : ℝ)^2 * rankCauchyCumulantWeight 16)) := by
  norm_num [rankCauchyConvolution, rankCauchyWeight, Finset.sum_Icc_succ_top]

theorem rankCauchy_root_allowance_square (r : ℕ) (hr : 2 ≤ r) (hr16 : r ≤ 16) :
    rankCauchyIntegralWeight (r-1) * rankCauchyConvolution r ≤
      (rankCauchyRootAllowance r)^2 := by
  interval_cases r
  · exact rankCauchyCertificate_2.1
  · exact rankCauchyCertificate_3.1
  · exact rankCauchyCertificate_4.1
  · exact rankCauchyCertificate_5.1
  · exact rankCauchyCertificate_6.1
  · exact rankCauchyCertificate_7.1
  · exact rankCauchyCertificate_8.1
  · exact rankCauchyCertificate_9.1
  · exact rankCauchyCertificate_10.1
  · exact rankCauchyCertificate_11.1
  · exact rankCauchyCertificate_12.1
  · exact rankCauchyCertificate_13.1
  · exact rankCauchyCertificate_14.1
  · exact rankCauchyCertificate_15.1
  · exact rankCauchyCertificate_16.1

theorem rankCauchy_integral_coefficient (r : ℕ) (hr : 2 ≤ r) (hr16 : r ≤ 16) :
    (((r+2 : ℕ) : ℝ) + 2*(r : ℝ)*(5*(r : ℝ)-2)) * rankCauchyIntegralWeight (r-1) +
      2 * rankCauchyRootAllowance r * (r : ℝ) ≤
        (3/7 : ℝ) * (r : ℝ)^2 * rankCauchyIntegralWeight r := by
  interval_cases r
  · exact rankCauchyCertificate_2.2.1
  · exact rankCauchyCertificate_3.2.1
  · exact rankCauchyCertificate_4.2.1
  · exact rankCauchyCertificate_5.2.1
  · exact rankCauchyCertificate_6.2.1
  · exact rankCauchyCertificate_7.2.1
  · exact rankCauchyCertificate_8.2.1
  · exact rankCauchyCertificate_9.2.1
  · exact rankCauchyCertificate_10.2.1
  · exact rankCauchyCertificate_11.2.1
  · exact rankCauchyCertificate_12.2.1
  · exact rankCauchyCertificate_13.2.1
  · exact rankCauchyCertificate_14.2.1
  · exact rankCauchyCertificate_15.2.1
  · exact rankCauchyCertificate_16.2.1

theorem rankCauchy_cumulant_coefficient (r : ℕ) (hr : 3 ≤ r) (hr16 : r ≤ 16) :
    (((r+2 : ℕ) : ℝ) + 4*(r : ℝ)*((r : ℝ)-1)) * rankCauchyIntegralWeight (r-1) +
      2 * rankCauchyRootAllowance r * (r : ℝ) ≤
        (r : ℝ)^2 * rankCauchyCumulantWeight r := by
  interval_cases r
  · exact rankCauchyCertificate_3.2.2 (by norm_num)
  · exact rankCauchyCertificate_4.2.2 (by norm_num)
  · exact rankCauchyCertificate_5.2.2 (by norm_num)
  · exact rankCauchyCertificate_6.2.2 (by norm_num)
  · exact rankCauchyCertificate_7.2.2 (by norm_num)
  · exact rankCauchyCertificate_8.2.2 (by norm_num)
  · exact rankCauchyCertificate_9.2.2 (by norm_num)
  · exact rankCauchyCertificate_10.2.2 (by norm_num)
  · exact rankCauchyCertificate_11.2.2 (by norm_num)
  · exact rankCauchyCertificate_12.2.2 (by norm_num)
  · exact rankCauchyCertificate_13.2.2 (by norm_num)
  · exact rankCauchyCertificate_14.2.2 (by norm_num)
  · exact rankCauchyCertificate_15.2.2 (by norm_num)
  · exact rankCauchyCertificate_16.2.2 (by norm_num)

end KLS.RouteArithmetic
end

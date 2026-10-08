import OptRankYoungWeights

/-! Exact finite-rank arithmetic certificates, with no floating-point
or native evaluation in the proof terms. -/
set_option maxHeartbeats 2000000
noncomputable section
namespace KLS.RouteArithmetic

theorem rankYoungCertificate_2 :
    (rankYoungIntegralWeight (2-1) * rankYoungConvolution 2 ≤
      (rankYoungRootAllowance 2)^2) ∧
    (((( 2+2 : ℕ) : ℝ) + 4*(2 : ℝ)*((2*rankYoungParameter 2-1)*(2 : ℝ)-1)) * rankYoungIntegralWeight (2-1) +
      2 * rankYoungRootAllowance 2 * (2 : ℝ) ≤
        rankYoungCoercivity 2 * (2 : ℝ)^2 * rankYoungIntegralWeight 2) ∧
    (3 ≤ 2 →
      (((( 2+2 : ℕ) : ℝ) + 4*(2 : ℝ)*((2 : ℝ)-1)) * rankYoungIntegralWeight (2-1) +
        2 * rankYoungRootAllowance 2 * (2 : ℝ) ≤
          (2 : ℝ)^2 * rankYoungCumulantWeight 2)) := by
  norm_num [rankYoungCoercivity, rankYoungConvolution, rankYoungCauchyWeight, Finset.sum_Icc_succ_top]

theorem rankYoungCertificate_3 :
    (rankYoungIntegralWeight (3-1) * rankYoungConvolution 3 ≤
      (rankYoungRootAllowance 3)^2) ∧
    (((( 3+2 : ℕ) : ℝ) + 4*(3 : ℝ)*((2*rankYoungParameter 3-1)*(3 : ℝ)-1)) * rankYoungIntegralWeight (3-1) +
      2 * rankYoungRootAllowance 3 * (3 : ℝ) ≤
        rankYoungCoercivity 3 * (3 : ℝ)^2 * rankYoungIntegralWeight 3) ∧
    (3 ≤ 3 →
      (((( 3+2 : ℕ) : ℝ) + 4*(3 : ℝ)*((3 : ℝ)-1)) * rankYoungIntegralWeight (3-1) +
        2 * rankYoungRootAllowance 3 * (3 : ℝ) ≤
          (3 : ℝ)^2 * rankYoungCumulantWeight 3)) := by
  norm_num [rankYoungCoercivity, rankYoungConvolution, rankYoungCauchyWeight, Finset.sum_Icc_succ_top]

theorem rankYoungCertificate_4 :
    (rankYoungIntegralWeight (4-1) * rankYoungConvolution 4 ≤
      (rankYoungRootAllowance 4)^2) ∧
    (((( 4+2 : ℕ) : ℝ) + 4*(4 : ℝ)*((2*rankYoungParameter 4-1)*(4 : ℝ)-1)) * rankYoungIntegralWeight (4-1) +
      2 * rankYoungRootAllowance 4 * (4 : ℝ) ≤
        rankYoungCoercivity 4 * (4 : ℝ)^2 * rankYoungIntegralWeight 4) ∧
    (3 ≤ 4 →
      (((( 4+2 : ℕ) : ℝ) + 4*(4 : ℝ)*((4 : ℝ)-1)) * rankYoungIntegralWeight (4-1) +
        2 * rankYoungRootAllowance 4 * (4 : ℝ) ≤
          (4 : ℝ)^2 * rankYoungCumulantWeight 4)) := by
  norm_num [rankYoungCoercivity, rankYoungConvolution, rankYoungCauchyWeight, Finset.sum_Icc_succ_top]

theorem rankYoungCertificate_5 :
    (rankYoungIntegralWeight (5-1) * rankYoungConvolution 5 ≤
      (rankYoungRootAllowance 5)^2) ∧
    (((( 5+2 : ℕ) : ℝ) + 4*(5 : ℝ)*((2*rankYoungParameter 5-1)*(5 : ℝ)-1)) * rankYoungIntegralWeight (5-1) +
      2 * rankYoungRootAllowance 5 * (5 : ℝ) ≤
        rankYoungCoercivity 5 * (5 : ℝ)^2 * rankYoungIntegralWeight 5) ∧
    (3 ≤ 5 →
      (((( 5+2 : ℕ) : ℝ) + 4*(5 : ℝ)*((5 : ℝ)-1)) * rankYoungIntegralWeight (5-1) +
        2 * rankYoungRootAllowance 5 * (5 : ℝ) ≤
          (5 : ℝ)^2 * rankYoungCumulantWeight 5)) := by
  norm_num [rankYoungCoercivity, rankYoungConvolution, rankYoungCauchyWeight, Finset.sum_Icc_succ_top]

theorem rankYoungCertificate_6 :
    (rankYoungIntegralWeight (6-1) * rankYoungConvolution 6 ≤
      (rankYoungRootAllowance 6)^2) ∧
    (((( 6+2 : ℕ) : ℝ) + 4*(6 : ℝ)*((2*rankYoungParameter 6-1)*(6 : ℝ)-1)) * rankYoungIntegralWeight (6-1) +
      2 * rankYoungRootAllowance 6 * (6 : ℝ) ≤
        rankYoungCoercivity 6 * (6 : ℝ)^2 * rankYoungIntegralWeight 6) ∧
    (3 ≤ 6 →
      (((( 6+2 : ℕ) : ℝ) + 4*(6 : ℝ)*((6 : ℝ)-1)) * rankYoungIntegralWeight (6-1) +
        2 * rankYoungRootAllowance 6 * (6 : ℝ) ≤
          (6 : ℝ)^2 * rankYoungCumulantWeight 6)) := by
  norm_num [rankYoungCoercivity, rankYoungConvolution, rankYoungCauchyWeight, Finset.sum_Icc_succ_top]

theorem rankYoungCertificate_7 :
    (rankYoungIntegralWeight (7-1) * rankYoungConvolution 7 ≤
      (rankYoungRootAllowance 7)^2) ∧
    (((( 7+2 : ℕ) : ℝ) + 4*(7 : ℝ)*((2*rankYoungParameter 7-1)*(7 : ℝ)-1)) * rankYoungIntegralWeight (7-1) +
      2 * rankYoungRootAllowance 7 * (7 : ℝ) ≤
        rankYoungCoercivity 7 * (7 : ℝ)^2 * rankYoungIntegralWeight 7) ∧
    (3 ≤ 7 →
      (((( 7+2 : ℕ) : ℝ) + 4*(7 : ℝ)*((7 : ℝ)-1)) * rankYoungIntegralWeight (7-1) +
        2 * rankYoungRootAllowance 7 * (7 : ℝ) ≤
          (7 : ℝ)^2 * rankYoungCumulantWeight 7)) := by
  norm_num [rankYoungCoercivity, rankYoungConvolution, rankYoungCauchyWeight, Finset.sum_Icc_succ_top]

theorem rankYoungCertificate_8 :
    (rankYoungIntegralWeight (8-1) * rankYoungConvolution 8 ≤
      (rankYoungRootAllowance 8)^2) ∧
    (((( 8+2 : ℕ) : ℝ) + 4*(8 : ℝ)*((2*rankYoungParameter 8-1)*(8 : ℝ)-1)) * rankYoungIntegralWeight (8-1) +
      2 * rankYoungRootAllowance 8 * (8 : ℝ) ≤
        rankYoungCoercivity 8 * (8 : ℝ)^2 * rankYoungIntegralWeight 8) ∧
    (3 ≤ 8 →
      (((( 8+2 : ℕ) : ℝ) + 4*(8 : ℝ)*((8 : ℝ)-1)) * rankYoungIntegralWeight (8-1) +
        2 * rankYoungRootAllowance 8 * (8 : ℝ) ≤
          (8 : ℝ)^2 * rankYoungCumulantWeight 8)) := by
  norm_num [rankYoungCoercivity, rankYoungConvolution, rankYoungCauchyWeight, Finset.sum_Icc_succ_top]

theorem rankYoungCertificate_9 :
    (rankYoungIntegralWeight (9-1) * rankYoungConvolution 9 ≤
      (rankYoungRootAllowance 9)^2) ∧
    (((( 9+2 : ℕ) : ℝ) + 4*(9 : ℝ)*((2*rankYoungParameter 9-1)*(9 : ℝ)-1)) * rankYoungIntegralWeight (9-1) +
      2 * rankYoungRootAllowance 9 * (9 : ℝ) ≤
        rankYoungCoercivity 9 * (9 : ℝ)^2 * rankYoungIntegralWeight 9) ∧
    (3 ≤ 9 →
      (((( 9+2 : ℕ) : ℝ) + 4*(9 : ℝ)*((9 : ℝ)-1)) * rankYoungIntegralWeight (9-1) +
        2 * rankYoungRootAllowance 9 * (9 : ℝ) ≤
          (9 : ℝ)^2 * rankYoungCumulantWeight 9)) := by
  norm_num [rankYoungCoercivity, rankYoungConvolution, rankYoungCauchyWeight, Finset.sum_Icc_succ_top]

theorem rankYoungCertificate_10 :
    (rankYoungIntegralWeight (10-1) * rankYoungConvolution 10 ≤
      (rankYoungRootAllowance 10)^2) ∧
    (((( 10+2 : ℕ) : ℝ) + 4*(10 : ℝ)*((2*rankYoungParameter 10-1)*(10 : ℝ)-1)) * rankYoungIntegralWeight (10-1) +
      2 * rankYoungRootAllowance 10 * (10 : ℝ) ≤
        rankYoungCoercivity 10 * (10 : ℝ)^2 * rankYoungIntegralWeight 10) ∧
    (3 ≤ 10 →
      (((( 10+2 : ℕ) : ℝ) + 4*(10 : ℝ)*((10 : ℝ)-1)) * rankYoungIntegralWeight (10-1) +
        2 * rankYoungRootAllowance 10 * (10 : ℝ) ≤
          (10 : ℝ)^2 * rankYoungCumulantWeight 10)) := by
  norm_num [rankYoungCoercivity, rankYoungConvolution, rankYoungCauchyWeight, Finset.sum_Icc_succ_top]

theorem rankYoungCertificate_11 :
    (rankYoungIntegralWeight (11-1) * rankYoungConvolution 11 ≤
      (rankYoungRootAllowance 11)^2) ∧
    (((( 11+2 : ℕ) : ℝ) + 4*(11 : ℝ)*((2*rankYoungParameter 11-1)*(11 : ℝ)-1)) * rankYoungIntegralWeight (11-1) +
      2 * rankYoungRootAllowance 11 * (11 : ℝ) ≤
        rankYoungCoercivity 11 * (11 : ℝ)^2 * rankYoungIntegralWeight 11) ∧
    (3 ≤ 11 →
      (((( 11+2 : ℕ) : ℝ) + 4*(11 : ℝ)*((11 : ℝ)-1)) * rankYoungIntegralWeight (11-1) +
        2 * rankYoungRootAllowance 11 * (11 : ℝ) ≤
          (11 : ℝ)^2 * rankYoungCumulantWeight 11)) := by
  norm_num [rankYoungCoercivity, rankYoungConvolution, rankYoungCauchyWeight, Finset.sum_Icc_succ_top]

theorem rankYoungCertificate_12 :
    (rankYoungIntegralWeight (12-1) * rankYoungConvolution 12 ≤
      (rankYoungRootAllowance 12)^2) ∧
    (((( 12+2 : ℕ) : ℝ) + 4*(12 : ℝ)*((2*rankYoungParameter 12-1)*(12 : ℝ)-1)) * rankYoungIntegralWeight (12-1) +
      2 * rankYoungRootAllowance 12 * (12 : ℝ) ≤
        rankYoungCoercivity 12 * (12 : ℝ)^2 * rankYoungIntegralWeight 12) ∧
    (3 ≤ 12 →
      (((( 12+2 : ℕ) : ℝ) + 4*(12 : ℝ)*((12 : ℝ)-1)) * rankYoungIntegralWeight (12-1) +
        2 * rankYoungRootAllowance 12 * (12 : ℝ) ≤
          (12 : ℝ)^2 * rankYoungCumulantWeight 12)) := by
  norm_num [rankYoungCoercivity, rankYoungConvolution, rankYoungCauchyWeight, Finset.sum_Icc_succ_top]

theorem rankYoungCertificate_13 :
    (rankYoungIntegralWeight (13-1) * rankYoungConvolution 13 ≤
      (rankYoungRootAllowance 13)^2) ∧
    (((( 13+2 : ℕ) : ℝ) + 4*(13 : ℝ)*((2*rankYoungParameter 13-1)*(13 : ℝ)-1)) * rankYoungIntegralWeight (13-1) +
      2 * rankYoungRootAllowance 13 * (13 : ℝ) ≤
        rankYoungCoercivity 13 * (13 : ℝ)^2 * rankYoungIntegralWeight 13) ∧
    (3 ≤ 13 →
      (((( 13+2 : ℕ) : ℝ) + 4*(13 : ℝ)*((13 : ℝ)-1)) * rankYoungIntegralWeight (13-1) +
        2 * rankYoungRootAllowance 13 * (13 : ℝ) ≤
          (13 : ℝ)^2 * rankYoungCumulantWeight 13)) := by
  norm_num [rankYoungCoercivity, rankYoungConvolution, rankYoungCauchyWeight, Finset.sum_Icc_succ_top]

theorem rankYoungCertificate_14 :
    (rankYoungIntegralWeight (14-1) * rankYoungConvolution 14 ≤
      (rankYoungRootAllowance 14)^2) ∧
    (((( 14+2 : ℕ) : ℝ) + 4*(14 : ℝ)*((2*rankYoungParameter 14-1)*(14 : ℝ)-1)) * rankYoungIntegralWeight (14-1) +
      2 * rankYoungRootAllowance 14 * (14 : ℝ) ≤
        rankYoungCoercivity 14 * (14 : ℝ)^2 * rankYoungIntegralWeight 14) ∧
    (3 ≤ 14 →
      (((( 14+2 : ℕ) : ℝ) + 4*(14 : ℝ)*((14 : ℝ)-1)) * rankYoungIntegralWeight (14-1) +
        2 * rankYoungRootAllowance 14 * (14 : ℝ) ≤
          (14 : ℝ)^2 * rankYoungCumulantWeight 14)) := by
  norm_num [rankYoungCoercivity, rankYoungConvolution, rankYoungCauchyWeight, Finset.sum_Icc_succ_top]

theorem rankYoungCertificate_15 :
    (rankYoungIntegralWeight (15-1) * rankYoungConvolution 15 ≤
      (rankYoungRootAllowance 15)^2) ∧
    (((( 15+2 : ℕ) : ℝ) + 4*(15 : ℝ)*((2*rankYoungParameter 15-1)*(15 : ℝ)-1)) * rankYoungIntegralWeight (15-1) +
      2 * rankYoungRootAllowance 15 * (15 : ℝ) ≤
        rankYoungCoercivity 15 * (15 : ℝ)^2 * rankYoungIntegralWeight 15) ∧
    (3 ≤ 15 →
      (((( 15+2 : ℕ) : ℝ) + 4*(15 : ℝ)*((15 : ℝ)-1)) * rankYoungIntegralWeight (15-1) +
        2 * rankYoungRootAllowance 15 * (15 : ℝ) ≤
          (15 : ℝ)^2 * rankYoungCumulantWeight 15)) := by
  norm_num [rankYoungCoercivity, rankYoungConvolution, rankYoungCauchyWeight, Finset.sum_Icc_succ_top]

theorem rankYoungCertificate_16 :
    (rankYoungIntegralWeight (16-1) * rankYoungConvolution 16 ≤
      (rankYoungRootAllowance 16)^2) ∧
    (((( 16+2 : ℕ) : ℝ) + 4*(16 : ℝ)*((2*rankYoungParameter 16-1)*(16 : ℝ)-1)) * rankYoungIntegralWeight (16-1) +
      2 * rankYoungRootAllowance 16 * (16 : ℝ) ≤
        rankYoungCoercivity 16 * (16 : ℝ)^2 * rankYoungIntegralWeight 16) ∧
    (3 ≤ 16 →
      (((( 16+2 : ℕ) : ℝ) + 4*(16 : ℝ)*((16 : ℝ)-1)) * rankYoungIntegralWeight (16-1) +
        2 * rankYoungRootAllowance 16 * (16 : ℝ) ≤
          (16 : ℝ)^2 * rankYoungCumulantWeight 16)) := by
  norm_num [rankYoungCoercivity, rankYoungConvolution, rankYoungCauchyWeight, Finset.sum_Icc_succ_top]

theorem rankYoung_root_allowance_square (r : ℕ) (hr : 2 ≤ r) (hr16 : r ≤ 16) :
    rankYoungIntegralWeight (r-1) * rankYoungConvolution r ≤
      (rankYoungRootAllowance r)^2 := by
  interval_cases r
  · exact rankYoungCertificate_2.1
  · exact rankYoungCertificate_3.1
  · exact rankYoungCertificate_4.1
  · exact rankYoungCertificate_5.1
  · exact rankYoungCertificate_6.1
  · exact rankYoungCertificate_7.1
  · exact rankYoungCertificate_8.1
  · exact rankYoungCertificate_9.1
  · exact rankYoungCertificate_10.1
  · exact rankYoungCertificate_11.1
  · exact rankYoungCertificate_12.1
  · exact rankYoungCertificate_13.1
  · exact rankYoungCertificate_14.1
  · exact rankYoungCertificate_15.1
  · exact rankYoungCertificate_16.1

theorem rankYoung_integral_coefficient (r : ℕ) (hr : 2 ≤ r) (hr16 : r ≤ 16) :
    (((r+2 : ℕ) : ℝ) + 4*(r : ℝ)*((2*rankYoungParameter r-1)*(r : ℝ)-1)) * rankYoungIntegralWeight (r-1) +
      2 * rankYoungRootAllowance r * (r : ℝ) ≤
        rankYoungCoercivity r * (r : ℝ)^2 * rankYoungIntegralWeight r := by
  interval_cases r
  · exact rankYoungCertificate_2.2.1
  · exact rankYoungCertificate_3.2.1
  · exact rankYoungCertificate_4.2.1
  · exact rankYoungCertificate_5.2.1
  · exact rankYoungCertificate_6.2.1
  · exact rankYoungCertificate_7.2.1
  · exact rankYoungCertificate_8.2.1
  · exact rankYoungCertificate_9.2.1
  · exact rankYoungCertificate_10.2.1
  · exact rankYoungCertificate_11.2.1
  · exact rankYoungCertificate_12.2.1
  · exact rankYoungCertificate_13.2.1
  · exact rankYoungCertificate_14.2.1
  · exact rankYoungCertificate_15.2.1
  · exact rankYoungCertificate_16.2.1

theorem rankYoung_cumulant_coefficient (r : ℕ) (hr : 3 ≤ r) (hr16 : r ≤ 16) :
    (((r+2 : ℕ) : ℝ) + 4*(r : ℝ)*((r : ℝ)-1)) * rankYoungIntegralWeight (r-1) +
      2 * rankYoungRootAllowance r * (r : ℝ) ≤
        (r : ℝ)^2 * rankYoungCumulantWeight r := by
  interval_cases r
  · exact rankYoungCertificate_3.2.2 (by norm_num)
  · exact rankYoungCertificate_4.2.2 (by norm_num)
  · exact rankYoungCertificate_5.2.2 (by norm_num)
  · exact rankYoungCertificate_6.2.2 (by norm_num)
  · exact rankYoungCertificate_7.2.2 (by norm_num)
  · exact rankYoungCertificate_8.2.2 (by norm_num)
  · exact rankYoungCertificate_9.2.2 (by norm_num)
  · exact rankYoungCertificate_10.2.2 (by norm_num)
  · exact rankYoungCertificate_11.2.2 (by norm_num)
  · exact rankYoungCertificate_12.2.2 (by norm_num)
  · exact rankYoungCertificate_13.2.2 (by norm_num)
  · exact rankYoungCertificate_14.2.2 (by norm_num)
  · exact rankYoungCertificate_15.2.2 (by norm_num)
  · exact rankYoungCertificate_16.2.2 (by norm_num)

end KLS.RouteArithmetic
end

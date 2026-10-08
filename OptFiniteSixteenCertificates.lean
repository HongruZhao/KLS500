import OptFiniteSixteenWeights

/-! Exact finite-rank arithmetic certificates, with no floating-point
or native evaluation in the proof terms. -/
set_option maxHeartbeats 2000000
noncomputable section
namespace KLS.RouteArithmetic

theorem finiteSixteenCertificate_2 :
    (finiteSixteenIntegralWeight (2-1) * ((2-2 : ℕ) : ℝ) * finiteSixteenRankConvolution 2 ≤
      (finiteSixteenRootAllowance 2)^2) ∧
    (((( 2+2 : ℕ) : ℝ) + 2*(2 : ℝ)*(5*(2 : ℝ)-2)) * finiteSixteenIntegralWeight (2-1) +
      2 * finiteSixteenRootAllowance 2 * (2 : ℝ) ≤
        (3/7 : ℝ) * (2 : ℝ)^2 * finiteSixteenIntegralWeight 2) ∧
    (3 ≤ 2 →
      (((( 2+2 : ℕ) : ℝ) + 4*(2 : ℝ)*((2 : ℝ)-1)) * finiteSixteenIntegralWeight (2-1) +
        2 * finiteSixteenRootAllowance 2 * (2 : ℝ) ≤
          (2 : ℝ)^2 * finiteSixteenCumulantWeight 2)) := by
  norm_num [finiteSixteenRankConvolution, Finset.sum_Icc_succ_top]

theorem finiteSixteenCertificate_3 :
    (finiteSixteenIntegralWeight (3-1) * ((3-2 : ℕ) : ℝ) * finiteSixteenRankConvolution 3 ≤
      (finiteSixteenRootAllowance 3)^2) ∧
    (((( 3+2 : ℕ) : ℝ) + 2*(3 : ℝ)*(5*(3 : ℝ)-2)) * finiteSixteenIntegralWeight (3-1) +
      2 * finiteSixteenRootAllowance 3 * (3 : ℝ) ≤
        (3/7 : ℝ) * (3 : ℝ)^2 * finiteSixteenIntegralWeight 3) ∧
    (3 ≤ 3 →
      (((( 3+2 : ℕ) : ℝ) + 4*(3 : ℝ)*((3 : ℝ)-1)) * finiteSixteenIntegralWeight (3-1) +
        2 * finiteSixteenRootAllowance 3 * (3 : ℝ) ≤
          (3 : ℝ)^2 * finiteSixteenCumulantWeight 3)) := by
  norm_num [finiteSixteenRankConvolution, Finset.sum_Icc_succ_top]

theorem finiteSixteenCertificate_4 :
    (finiteSixteenIntegralWeight (4-1) * ((4-2 : ℕ) : ℝ) * finiteSixteenRankConvolution 4 ≤
      (finiteSixteenRootAllowance 4)^2) ∧
    (((( 4+2 : ℕ) : ℝ) + 2*(4 : ℝ)*(5*(4 : ℝ)-2)) * finiteSixteenIntegralWeight (4-1) +
      2 * finiteSixteenRootAllowance 4 * (4 : ℝ) ≤
        (3/7 : ℝ) * (4 : ℝ)^2 * finiteSixteenIntegralWeight 4) ∧
    (3 ≤ 4 →
      (((( 4+2 : ℕ) : ℝ) + 4*(4 : ℝ)*((4 : ℝ)-1)) * finiteSixteenIntegralWeight (4-1) +
        2 * finiteSixteenRootAllowance 4 * (4 : ℝ) ≤
          (4 : ℝ)^2 * finiteSixteenCumulantWeight 4)) := by
  norm_num [finiteSixteenRankConvolution, Finset.sum_Icc_succ_top]

theorem finiteSixteenCertificate_5 :
    (finiteSixteenIntegralWeight (5-1) * ((5-2 : ℕ) : ℝ) * finiteSixteenRankConvolution 5 ≤
      (finiteSixteenRootAllowance 5)^2) ∧
    (((( 5+2 : ℕ) : ℝ) + 2*(5 : ℝ)*(5*(5 : ℝ)-2)) * finiteSixteenIntegralWeight (5-1) +
      2 * finiteSixteenRootAllowance 5 * (5 : ℝ) ≤
        (3/7 : ℝ) * (5 : ℝ)^2 * finiteSixteenIntegralWeight 5) ∧
    (3 ≤ 5 →
      (((( 5+2 : ℕ) : ℝ) + 4*(5 : ℝ)*((5 : ℝ)-1)) * finiteSixteenIntegralWeight (5-1) +
        2 * finiteSixteenRootAllowance 5 * (5 : ℝ) ≤
          (5 : ℝ)^2 * finiteSixteenCumulantWeight 5)) := by
  norm_num [finiteSixteenRankConvolution, Finset.sum_Icc_succ_top]

theorem finiteSixteenCertificate_6 :
    (finiteSixteenIntegralWeight (6-1) * ((6-2 : ℕ) : ℝ) * finiteSixteenRankConvolution 6 ≤
      (finiteSixteenRootAllowance 6)^2) ∧
    (((( 6+2 : ℕ) : ℝ) + 2*(6 : ℝ)*(5*(6 : ℝ)-2)) * finiteSixteenIntegralWeight (6-1) +
      2 * finiteSixteenRootAllowance 6 * (6 : ℝ) ≤
        (3/7 : ℝ) * (6 : ℝ)^2 * finiteSixteenIntegralWeight 6) ∧
    (3 ≤ 6 →
      (((( 6+2 : ℕ) : ℝ) + 4*(6 : ℝ)*((6 : ℝ)-1)) * finiteSixteenIntegralWeight (6-1) +
        2 * finiteSixteenRootAllowance 6 * (6 : ℝ) ≤
          (6 : ℝ)^2 * finiteSixteenCumulantWeight 6)) := by
  norm_num [finiteSixteenRankConvolution, Finset.sum_Icc_succ_top]

theorem finiteSixteenCertificate_7 :
    (finiteSixteenIntegralWeight (7-1) * ((7-2 : ℕ) : ℝ) * finiteSixteenRankConvolution 7 ≤
      (finiteSixteenRootAllowance 7)^2) ∧
    (((( 7+2 : ℕ) : ℝ) + 2*(7 : ℝ)*(5*(7 : ℝ)-2)) * finiteSixteenIntegralWeight (7-1) +
      2 * finiteSixteenRootAllowance 7 * (7 : ℝ) ≤
        (3/7 : ℝ) * (7 : ℝ)^2 * finiteSixteenIntegralWeight 7) ∧
    (3 ≤ 7 →
      (((( 7+2 : ℕ) : ℝ) + 4*(7 : ℝ)*((7 : ℝ)-1)) * finiteSixteenIntegralWeight (7-1) +
        2 * finiteSixteenRootAllowance 7 * (7 : ℝ) ≤
          (7 : ℝ)^2 * finiteSixteenCumulantWeight 7)) := by
  norm_num [finiteSixteenRankConvolution, Finset.sum_Icc_succ_top]

theorem finiteSixteenCertificate_8 :
    (finiteSixteenIntegralWeight (8-1) * ((8-2 : ℕ) : ℝ) * finiteSixteenRankConvolution 8 ≤
      (finiteSixteenRootAllowance 8)^2) ∧
    (((( 8+2 : ℕ) : ℝ) + 2*(8 : ℝ)*(5*(8 : ℝ)-2)) * finiteSixteenIntegralWeight (8-1) +
      2 * finiteSixteenRootAllowance 8 * (8 : ℝ) ≤
        (3/7 : ℝ) * (8 : ℝ)^2 * finiteSixteenIntegralWeight 8) ∧
    (3 ≤ 8 →
      (((( 8+2 : ℕ) : ℝ) + 4*(8 : ℝ)*((8 : ℝ)-1)) * finiteSixteenIntegralWeight (8-1) +
        2 * finiteSixteenRootAllowance 8 * (8 : ℝ) ≤
          (8 : ℝ)^2 * finiteSixteenCumulantWeight 8)) := by
  norm_num [finiteSixteenRankConvolution, Finset.sum_Icc_succ_top]

theorem finiteSixteenCertificate_9 :
    (finiteSixteenIntegralWeight (9-1) * ((9-2 : ℕ) : ℝ) * finiteSixteenRankConvolution 9 ≤
      (finiteSixteenRootAllowance 9)^2) ∧
    (((( 9+2 : ℕ) : ℝ) + 2*(9 : ℝ)*(5*(9 : ℝ)-2)) * finiteSixteenIntegralWeight (9-1) +
      2 * finiteSixteenRootAllowance 9 * (9 : ℝ) ≤
        (3/7 : ℝ) * (9 : ℝ)^2 * finiteSixteenIntegralWeight 9) ∧
    (3 ≤ 9 →
      (((( 9+2 : ℕ) : ℝ) + 4*(9 : ℝ)*((9 : ℝ)-1)) * finiteSixteenIntegralWeight (9-1) +
        2 * finiteSixteenRootAllowance 9 * (9 : ℝ) ≤
          (9 : ℝ)^2 * finiteSixteenCumulantWeight 9)) := by
  norm_num [finiteSixteenRankConvolution, Finset.sum_Icc_succ_top]

theorem finiteSixteenCertificate_10 :
    (finiteSixteenIntegralWeight (10-1) * ((10-2 : ℕ) : ℝ) * finiteSixteenRankConvolution 10 ≤
      (finiteSixteenRootAllowance 10)^2) ∧
    (((( 10+2 : ℕ) : ℝ) + 2*(10 : ℝ)*(5*(10 : ℝ)-2)) * finiteSixteenIntegralWeight (10-1) +
      2 * finiteSixteenRootAllowance 10 * (10 : ℝ) ≤
        (3/7 : ℝ) * (10 : ℝ)^2 * finiteSixteenIntegralWeight 10) ∧
    (3 ≤ 10 →
      (((( 10+2 : ℕ) : ℝ) + 4*(10 : ℝ)*((10 : ℝ)-1)) * finiteSixteenIntegralWeight (10-1) +
        2 * finiteSixteenRootAllowance 10 * (10 : ℝ) ≤
          (10 : ℝ)^2 * finiteSixteenCumulantWeight 10)) := by
  norm_num [finiteSixteenRankConvolution, Finset.sum_Icc_succ_top]

theorem finiteSixteenCertificate_11 :
    (finiteSixteenIntegralWeight (11-1) * ((11-2 : ℕ) : ℝ) * finiteSixteenRankConvolution 11 ≤
      (finiteSixteenRootAllowance 11)^2) ∧
    (((( 11+2 : ℕ) : ℝ) + 2*(11 : ℝ)*(5*(11 : ℝ)-2)) * finiteSixteenIntegralWeight (11-1) +
      2 * finiteSixteenRootAllowance 11 * (11 : ℝ) ≤
        (3/7 : ℝ) * (11 : ℝ)^2 * finiteSixteenIntegralWeight 11) ∧
    (3 ≤ 11 →
      (((( 11+2 : ℕ) : ℝ) + 4*(11 : ℝ)*((11 : ℝ)-1)) * finiteSixteenIntegralWeight (11-1) +
        2 * finiteSixteenRootAllowance 11 * (11 : ℝ) ≤
          (11 : ℝ)^2 * finiteSixteenCumulantWeight 11)) := by
  norm_num [finiteSixteenRankConvolution, Finset.sum_Icc_succ_top]

theorem finiteSixteenCertificate_12 :
    (finiteSixteenIntegralWeight (12-1) * ((12-2 : ℕ) : ℝ) * finiteSixteenRankConvolution 12 ≤
      (finiteSixteenRootAllowance 12)^2) ∧
    (((( 12+2 : ℕ) : ℝ) + 2*(12 : ℝ)*(5*(12 : ℝ)-2)) * finiteSixteenIntegralWeight (12-1) +
      2 * finiteSixteenRootAllowance 12 * (12 : ℝ) ≤
        (3/7 : ℝ) * (12 : ℝ)^2 * finiteSixteenIntegralWeight 12) ∧
    (3 ≤ 12 →
      (((( 12+2 : ℕ) : ℝ) + 4*(12 : ℝ)*((12 : ℝ)-1)) * finiteSixteenIntegralWeight (12-1) +
        2 * finiteSixteenRootAllowance 12 * (12 : ℝ) ≤
          (12 : ℝ)^2 * finiteSixteenCumulantWeight 12)) := by
  norm_num [finiteSixteenRankConvolution, Finset.sum_Icc_succ_top]

theorem finiteSixteenCertificate_13 :
    (finiteSixteenIntegralWeight (13-1) * ((13-2 : ℕ) : ℝ) * finiteSixteenRankConvolution 13 ≤
      (finiteSixteenRootAllowance 13)^2) ∧
    (((( 13+2 : ℕ) : ℝ) + 2*(13 : ℝ)*(5*(13 : ℝ)-2)) * finiteSixteenIntegralWeight (13-1) +
      2 * finiteSixteenRootAllowance 13 * (13 : ℝ) ≤
        (3/7 : ℝ) * (13 : ℝ)^2 * finiteSixteenIntegralWeight 13) ∧
    (3 ≤ 13 →
      (((( 13+2 : ℕ) : ℝ) + 4*(13 : ℝ)*((13 : ℝ)-1)) * finiteSixteenIntegralWeight (13-1) +
        2 * finiteSixteenRootAllowance 13 * (13 : ℝ) ≤
          (13 : ℝ)^2 * finiteSixteenCumulantWeight 13)) := by
  norm_num [finiteSixteenRankConvolution, Finset.sum_Icc_succ_top]

theorem finiteSixteenCertificate_14 :
    (finiteSixteenIntegralWeight (14-1) * ((14-2 : ℕ) : ℝ) * finiteSixteenRankConvolution 14 ≤
      (finiteSixteenRootAllowance 14)^2) ∧
    (((( 14+2 : ℕ) : ℝ) + 2*(14 : ℝ)*(5*(14 : ℝ)-2)) * finiteSixteenIntegralWeight (14-1) +
      2 * finiteSixteenRootAllowance 14 * (14 : ℝ) ≤
        (3/7 : ℝ) * (14 : ℝ)^2 * finiteSixteenIntegralWeight 14) ∧
    (3 ≤ 14 →
      (((( 14+2 : ℕ) : ℝ) + 4*(14 : ℝ)*((14 : ℝ)-1)) * finiteSixteenIntegralWeight (14-1) +
        2 * finiteSixteenRootAllowance 14 * (14 : ℝ) ≤
          (14 : ℝ)^2 * finiteSixteenCumulantWeight 14)) := by
  norm_num [finiteSixteenRankConvolution, Finset.sum_Icc_succ_top]

theorem finiteSixteenCertificate_15 :
    (finiteSixteenIntegralWeight (15-1) * ((15-2 : ℕ) : ℝ) * finiteSixteenRankConvolution 15 ≤
      (finiteSixteenRootAllowance 15)^2) ∧
    (((( 15+2 : ℕ) : ℝ) + 2*(15 : ℝ)*(5*(15 : ℝ)-2)) * finiteSixteenIntegralWeight (15-1) +
      2 * finiteSixteenRootAllowance 15 * (15 : ℝ) ≤
        (3/7 : ℝ) * (15 : ℝ)^2 * finiteSixteenIntegralWeight 15) ∧
    (3 ≤ 15 →
      (((( 15+2 : ℕ) : ℝ) + 4*(15 : ℝ)*((15 : ℝ)-1)) * finiteSixteenIntegralWeight (15-1) +
        2 * finiteSixteenRootAllowance 15 * (15 : ℝ) ≤
          (15 : ℝ)^2 * finiteSixteenCumulantWeight 15)) := by
  norm_num [finiteSixteenRankConvolution, Finset.sum_Icc_succ_top]

theorem finiteSixteenCertificate_16 :
    (finiteSixteenIntegralWeight (16-1) * ((16-2 : ℕ) : ℝ) * finiteSixteenRankConvolution 16 ≤
      (finiteSixteenRootAllowance 16)^2) ∧
    (((( 16+2 : ℕ) : ℝ) + 2*(16 : ℝ)*(5*(16 : ℝ)-2)) * finiteSixteenIntegralWeight (16-1) +
      2 * finiteSixteenRootAllowance 16 * (16 : ℝ) ≤
        (3/7 : ℝ) * (16 : ℝ)^2 * finiteSixteenIntegralWeight 16) ∧
    (3 ≤ 16 →
      (((( 16+2 : ℕ) : ℝ) + 4*(16 : ℝ)*((16 : ℝ)-1)) * finiteSixteenIntegralWeight (16-1) +
        2 * finiteSixteenRootAllowance 16 * (16 : ℝ) ≤
          (16 : ℝ)^2 * finiteSixteenCumulantWeight 16)) := by
  norm_num [finiteSixteenRankConvolution, Finset.sum_Icc_succ_top]

theorem finiteSixteen_root_allowance_square (r : ℕ) (hr : 2 ≤ r) (hr16 : r ≤ 16) :
    finiteSixteenIntegralWeight (r-1) * ((r-2 : ℕ) : ℝ) * finiteSixteenRankConvolution r ≤
      (finiteSixteenRootAllowance r)^2 := by
  interval_cases r
  · exact finiteSixteenCertificate_2.1
  · exact finiteSixteenCertificate_3.1
  · exact finiteSixteenCertificate_4.1
  · exact finiteSixteenCertificate_5.1
  · exact finiteSixteenCertificate_6.1
  · exact finiteSixteenCertificate_7.1
  · exact finiteSixteenCertificate_8.1
  · exact finiteSixteenCertificate_9.1
  · exact finiteSixteenCertificate_10.1
  · exact finiteSixteenCertificate_11.1
  · exact finiteSixteenCertificate_12.1
  · exact finiteSixteenCertificate_13.1
  · exact finiteSixteenCertificate_14.1
  · exact finiteSixteenCertificate_15.1
  · exact finiteSixteenCertificate_16.1

theorem finiteSixteen_integral_coefficient (r : ℕ) (hr : 2 ≤ r) (hr16 : r ≤ 16) :
    (((r+2 : ℕ) : ℝ) + 2*(r : ℝ)*(5*(r : ℝ)-2)) * finiteSixteenIntegralWeight (r-1) +
      2 * finiteSixteenRootAllowance r * (r : ℝ) ≤
        (3/7 : ℝ) * (r : ℝ)^2 * finiteSixteenIntegralWeight r := by
  interval_cases r
  · exact finiteSixteenCertificate_2.2.1
  · exact finiteSixteenCertificate_3.2.1
  · exact finiteSixteenCertificate_4.2.1
  · exact finiteSixteenCertificate_5.2.1
  · exact finiteSixteenCertificate_6.2.1
  · exact finiteSixteenCertificate_7.2.1
  · exact finiteSixteenCertificate_8.2.1
  · exact finiteSixteenCertificate_9.2.1
  · exact finiteSixteenCertificate_10.2.1
  · exact finiteSixteenCertificate_11.2.1
  · exact finiteSixteenCertificate_12.2.1
  · exact finiteSixteenCertificate_13.2.1
  · exact finiteSixteenCertificate_14.2.1
  · exact finiteSixteenCertificate_15.2.1
  · exact finiteSixteenCertificate_16.2.1

theorem finiteSixteen_cumulant_coefficient (r : ℕ) (hr : 3 ≤ r) (hr16 : r ≤ 16) :
    (((r+2 : ℕ) : ℝ) + 4*(r : ℝ)*((r : ℝ)-1)) * finiteSixteenIntegralWeight (r-1) +
      2 * finiteSixteenRootAllowance r * (r : ℝ) ≤
        (r : ℝ)^2 * finiteSixteenCumulantWeight r := by
  interval_cases r
  · exact finiteSixteenCertificate_3.2.2 (by norm_num)
  · exact finiteSixteenCertificate_4.2.2 (by norm_num)
  · exact finiteSixteenCertificate_5.2.2 (by norm_num)
  · exact finiteSixteenCertificate_6.2.2 (by norm_num)
  · exact finiteSixteenCertificate_7.2.2 (by norm_num)
  · exact finiteSixteenCertificate_8.2.2 (by norm_num)
  · exact finiteSixteenCertificate_9.2.2 (by norm_num)
  · exact finiteSixteenCertificate_10.2.2 (by norm_num)
  · exact finiteSixteenCertificate_11.2.2 (by norm_num)
  · exact finiteSixteenCertificate_12.2.2 (by norm_num)
  · exact finiteSixteenCertificate_13.2.2 (by norm_num)
  · exact finiteSixteenCertificate_14.2.2 (by norm_num)
  · exact finiteSixteenCertificate_15.2.2 (by norm_num)
  · exact finiteSixteenCertificate_16.2.2 (by norm_num)

end KLS.RouteArithmetic
end

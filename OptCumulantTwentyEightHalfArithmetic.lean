import OptTwentyEightHalfConvolution
import OptTwentyEightHalfFinite2To12
import OptTwentyEightHalfFinite13To23
import OptTwentyEightHalfFinite24To34

/-! Rational certificates for the finite ranks and a uniform proof for
all later ranks with the three-sevenths energy coefficient. -/
set_option maxHeartbeats 8000000
noncomputable section
namespace KLS.RouteArithmetic

theorem twentyEightHalfRootAllowance_square (r : ℕ) (hr : 2 ≤ r) :
    (40033/6000 : ℝ) * twentyEightHalfIntegralWeight (r-1) * ((r-2 : ℕ) : ℝ) *
      twentyEightHalfRankConvolution r ≤ (twentyEightHalfRootAllowance r)^2 := by
  by_cases hlarge : 35 ≤ r
  · rw [twentyEightHalfRootAllowance_large hlarge]
    have hq := twentyEightHalfIntegralWeight_le_one (by omega : 18 ≤ r-1)
    have hS := twentyEightHalfRankConvolution_nonneg r
    have hh := mul_le_mul_of_nonneg_right hq
      (mul_nonneg (Nat.cast_nonneg (α := ℝ) (r-2)) hS)
    have hc := twentyEightHalfRankConvolution_bound hlarge
    nlinarith [sq_nonneg ((r : ℝ)+9/8)]
  · interval_cases r
    · exact twentyEightHalfFiniteCertificate_2.1
    · exact twentyEightHalfFiniteCertificate_3.1
    · exact twentyEightHalfFiniteCertificate_4.1
    · exact twentyEightHalfFiniteCertificate_5.1
    · exact twentyEightHalfFiniteCertificate_6.1
    · exact twentyEightHalfFiniteCertificate_7.1
    · exact twentyEightHalfFiniteCertificate_8.1
    · exact twentyEightHalfFiniteCertificate_9.1
    · exact twentyEightHalfFiniteCertificate_10.1
    · exact twentyEightHalfFiniteCertificate_11.1
    · exact twentyEightHalfFiniteCertificate_12.1
    · exact twentyEightHalfFiniteCertificate_13.1
    · exact twentyEightHalfFiniteCertificate_14.1
    · exact twentyEightHalfFiniteCertificate_15.1
    · exact twentyEightHalfFiniteCertificate_16.1
    · exact twentyEightHalfFiniteCertificate_17.1
    · exact twentyEightHalfFiniteCertificate_18.1
    · exact twentyEightHalfFiniteCertificate_19.1
    · exact twentyEightHalfFiniteCertificate_20.1
    · exact twentyEightHalfFiniteCertificate_21.1
    · exact twentyEightHalfFiniteCertificate_22.1
    · exact twentyEightHalfFiniteCertificate_23.1
    · exact twentyEightHalfFiniteCertificate_24.1
    · exact twentyEightHalfFiniteCertificate_25.1
    · exact twentyEightHalfFiniteCertificate_26.1
    · exact twentyEightHalfFiniteCertificate_27.1
    · exact twentyEightHalfFiniteCertificate_28.1
    · exact twentyEightHalfFiniteCertificate_29.1
    · exact twentyEightHalfFiniteCertificate_30.1
    · exact twentyEightHalfFiniteCertificate_31.1
    · exact twentyEightHalfFiniteCertificate_32.1
    · exact twentyEightHalfFiniteCertificate_33.1
    · exact twentyEightHalfFiniteCertificate_34.1

theorem twentyEightHalfRank_coefficient (r : ℕ) (hr : 2 ≤ r) :
    (7/3 : ℝ) * (((r+2 : ℕ) : ℝ) + 2*(r : ℝ)*(5*(r : ℝ)-2)) * twentyEightHalfIntegralWeight (r-1) +
      2 * twentyEightHalfRootAllowance r * (r : ℝ) ≤ (57/2 : ℝ) * (r : ℝ)^2 * twentyEightHalfIntegralWeight r := by
  by_cases hlarge : 35 ≤ r
  · rw [twentyEightHalfRootAllowance_large hlarge, twentyEightHalfIntegralWeight_large (by omega : 33 ≤ r)]
    have hr' : (35 : ℝ) ≤ r := by exact_mod_cast hlarge
    have hq := twentyEightHalfIntegralWeight_le_one (by omega : 18 ≤ r-1)
    have hfac : 0 ≤ 5*(r : ℝ)-2 := by linarith
    have hh := mul_le_mul_of_nonneg_left hq
      (show 0 ≤ (7/3 : ℝ) * (((r+2 : ℕ) : ℝ) + 2*(r : ℝ)*(5*(r : ℝ)-2)) by positivity)
    push_cast at hh ⊢
    nlinarith [sq_nonneg ((r : ℝ)-35)]
  · interval_cases r
    · exact twentyEightHalfFiniteCertificate_2.2
    · exact twentyEightHalfFiniteCertificate_3.2
    · exact twentyEightHalfFiniteCertificate_4.2
    · exact twentyEightHalfFiniteCertificate_5.2
    · exact twentyEightHalfFiniteCertificate_6.2
    · exact twentyEightHalfFiniteCertificate_7.2
    · exact twentyEightHalfFiniteCertificate_8.2
    · exact twentyEightHalfFiniteCertificate_9.2
    · exact twentyEightHalfFiniteCertificate_10.2
    · exact twentyEightHalfFiniteCertificate_11.2
    · exact twentyEightHalfFiniteCertificate_12.2
    · exact twentyEightHalfFiniteCertificate_13.2
    · exact twentyEightHalfFiniteCertificate_14.2
    · exact twentyEightHalfFiniteCertificate_15.2
    · exact twentyEightHalfFiniteCertificate_16.2
    · exact twentyEightHalfFiniteCertificate_17.2
    · exact twentyEightHalfFiniteCertificate_18.2
    · exact twentyEightHalfFiniteCertificate_19.2
    · exact twentyEightHalfFiniteCertificate_20.2
    · exact twentyEightHalfFiniteCertificate_21.2
    · exact twentyEightHalfFiniteCertificate_22.2
    · exact twentyEightHalfFiniteCertificate_23.2
    · exact twentyEightHalfFiniteCertificate_24.2
    · exact twentyEightHalfFiniteCertificate_25.2
    · exact twentyEightHalfFiniteCertificate_26.2
    · exact twentyEightHalfFiniteCertificate_27.2
    · exact twentyEightHalfFiniteCertificate_28.2
    · exact twentyEightHalfFiniteCertificate_29.2
    · exact twentyEightHalfFiniteCertificate_30.2
    · exact twentyEightHalfFiniteCertificate_31.2
    · exact twentyEightHalfFiniteCertificate_32.2
    · exact twentyEightHalfFiniteCertificate_33.2
    · exact twentyEightHalfFiniteCertificate_34.2

theorem energy_induction_scalar_step_twentyEightHalf (r : ℕ) (hr : 2 ≤ r)
    {P B e l : ℝ} (hP : 0 ≤ P) (he0 : 0 ≤ e) (hl0 : 0 ≤ l)
    (hB : B = (57/2 : ℝ) * (r : ℝ)^2 * twentyEightHalfIntegralWeight r * P)
    (he : e ≤ (7/3 : ℝ) * twentyEightHalfIntegralWeight (r-1) * P)
    (hl : l ≤ (5719/2000 : ℝ) * ((r-2 : ℕ) : ℝ) * twentyEightHalfRankConvolution r * (r : ℝ)^2 * P) :
    (((r+2 : ℕ) : ℝ) + 2*(r : ℝ)*(5*(r : ℝ)-2)) * e +
      2 * Real.sqrt e * Real.sqrt l ≤ B := by
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hq : 0 ≤ twentyEightHalfIntegralWeight (r-1) := (twentyEightHalfIntegralWeight_pos _).le
  have ha : 0 ≤ twentyEightHalfRootAllowance r := twentyEightHalfRootAllowance_nonneg r
  have hroot : Real.sqrt e * Real.sqrt l ≤ twentyEightHalfRootAllowance r * (r : ℝ) * P := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt he0, Real.sq_sqrt hl0]
    calc
      e*l ≤ ((7/3 : ℝ) * twentyEightHalfIntegralWeight (r-1) * P) *
          ((5719/2000 : ℝ) * ((r-2 : ℕ) : ℝ) * twentyEightHalfRankConvolution r * (r : ℝ)^2 * P) :=
        mul_le_mul he hl hl0 (by positivity)
      _ = ((40033/6000 : ℝ) * twentyEightHalfIntegralWeight (r-1) * ((r-2 : ℕ) : ℝ) *
          twentyEightHalfRankConvolution r) * ((r : ℝ)*P)^2 := by ring
      _ ≤ (twentyEightHalfRootAllowance r)^2 * ((r : ℝ)*P)^2 :=
        mul_le_mul_of_nonneg_right (twentyEightHalfRootAllowance_square r hr) (sq_nonneg _)
      _ = (twentyEightHalfRootAllowance r * (r : ℝ) * P)^2 := by ring
  have hfactor : 0 ≤ 5*(r : ℝ)-2 := by linarith
  have hmain := mul_le_mul_of_nonneg_left he
    (show 0 ≤ (((r+2 : ℕ) : ℝ) + 2*(r : ℝ)*(5*(r : ℝ)-2)) by positivity)
  have hcoef := mul_le_mul_of_nonneg_right (twentyEightHalfRank_coefficient r hr) hP
  rw [hB]
  nlinarith

end KLS.RouteArithmetic
end

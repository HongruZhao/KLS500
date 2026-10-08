import OptTwentyNineRankWeights

/-! Rational certificates for the finite ranks and a uniform proof for
all later ranks with the three-sevenths energy coefficient. -/
set_option maxHeartbeats 4000000
noncomputable section
namespace KLS.RouteArithmetic

theorem twentyNineRootAllowance_square (r : ℕ) (hr : 2 ≤ r) :
    (1421/180 : ℝ) * twentyNineRankWeight (r-1) * ((r-2 : ℕ) : ℝ) *
      twentyNineRankConvolution r ≤ (twentyNineRootAllowance r)^2 := by
  by_cases hlarge : 26 ≤ r
  · rw [twentyNineRootAllowance_large hlarge]
    have hq := twentyNineRankWeight_le_one (by omega : 12 ≤ r-1)
    have hS := twentyNineRankConvolution_nonneg r
    have hh := mul_le_mul_of_nonneg_right hq
      (mul_nonneg (Nat.cast_nonneg (α := ℝ) (r-2)) hS)
    have hc := twentyNineRankConvolution_bound hlarge
    nlinarith [sq_nonneg ((r : ℝ)+7/5)]
  · interval_cases r <;> norm_num [twentyNineRankWeight, twentyNineRankConvolution,
      twentyNineRootAllowance, Finset.sum_Icc_succ_top]

theorem twentyNineRank_coefficient (r : ℕ) (hr : 2 ≤ r) :
    (7/3 : ℝ) * (((r+2 : ℕ) : ℝ) + 2*(r : ℝ)*(5*(r : ℝ)-2)) * twentyNineRankWeight (r-1) +
      2 * twentyNineRootAllowance r * (r : ℝ) ≤ 29 * (r : ℝ)^2 * twentyNineRankWeight r := by
  by_cases hlarge : 26 ≤ r
  · rw [twentyNineRootAllowance_large hlarge, twentyNineRankWeight_large hlarge]
    have hr' : (26 : ℝ) ≤ r := by exact_mod_cast hlarge
    have hq := twentyNineRankWeight_le_one (by omega : 12 ≤ r-1)
    have hfac : 0 ≤ 5*(r : ℝ)-2 := by linarith
    have hh := mul_le_mul_of_nonneg_left hq
      (show 0 ≤ (7/3 : ℝ) * (((r+2 : ℕ) : ℝ) + 2*(r : ℝ)*(5*(r : ℝ)-2)) by positivity)
    push_cast at hh ⊢
    nlinarith [sq_nonneg ((r : ℝ)-26)]
  · interval_cases r <;> norm_num [twentyNineRootAllowance, twentyNineRankWeight]

theorem energy_induction_scalar_step_twentyNine (r : ℕ) (hr : 2 ≤ r)
    {P B e l : ℝ} (hP : 0 ≤ P) (he0 : 0 ≤ e) (hl0 : 0 ≤ l)
    (hB : B = 29 * (r : ℝ)^2 * twentyNineRankWeight r * P)
    (he : e ≤ (7/3 : ℝ) * twentyNineRankWeight (r-1) * P)
    (hl : l ≤ (203/60 : ℝ) * ((r-2 : ℕ) : ℝ) * twentyNineRankConvolution r * (r : ℝ)^2 * P) :
    (((r+2 : ℕ) : ℝ) + 2*(r : ℝ)*(5*(r : ℝ)-2)) * e +
      2 * Real.sqrt e * Real.sqrt l ≤ B := by
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hq : 0 ≤ twentyNineRankWeight (r-1) := (twentyNineRankWeight_pos _).le
  have ha : 0 ≤ twentyNineRootAllowance r := twentyNineRootAllowance_nonneg r
  have hroot : Real.sqrt e * Real.sqrt l ≤ twentyNineRootAllowance r * (r : ℝ) * P := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt he0, Real.sq_sqrt hl0]
    calc
      e*l ≤ ((7/3 : ℝ) * twentyNineRankWeight (r-1) * P) *
          ((203/60 : ℝ) * ((r-2 : ℕ) : ℝ) * twentyNineRankConvolution r * (r : ℝ)^2 * P) :=
        mul_le_mul he hl hl0 (by positivity)
      _ = ((1421/180 : ℝ) * twentyNineRankWeight (r-1) * ((r-2 : ℕ) : ℝ) *
          twentyNineRankConvolution r) * ((r : ℝ)*P)^2 := by ring
      _ ≤ (twentyNineRootAllowance r)^2 * ((r : ℝ)*P)^2 :=
        mul_le_mul_of_nonneg_right (twentyNineRootAllowance_square r hr) (sq_nonneg _)
      _ = (twentyNineRootAllowance r * (r : ℝ) * P)^2 := by ring
  have hfactor : 0 ≤ 5*(r : ℝ)-2 := by linarith
  have hmain := mul_le_mul_of_nonneg_left he
    (show 0 ≤ (((r+2 : ℕ) : ℝ) + 2*(r : ℝ)*(5*(r : ℝ)-2)) by positivity)
  have hcoef := mul_le_mul_of_nonneg_right (twentyNineRank_coefficient r hr) hP
  rw [hB]
  nlinarith

end KLS.RouteArithmetic
end

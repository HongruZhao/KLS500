import Mathlib

/-! Scalar induction arithmetic for the proved energy drift C=17 and K=144.
The direct factor estimate replaces the paper's sufficient condition K>=9C.
No probabilistic or cumulant bound is asserted by this module. -/
noncomputable section
namespace KLS.RouteArithmetic

theorem induction_factor_seventeen_le_eightyThree_ninetySixths (m : ℕ) (hm : 3 ≤ m) :
    (34 / 144 : ℝ) * (m : ℝ)^2 / ((m : ℝ)-1)^2 +
      (1/3 : ℝ) * ((m : ℝ)-3) / ((m : ℝ)-1) ≤ 83/96 := by
  have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hd : 0 < (m : ℝ)-1 := by linarith
  have hfirst : (34/144 : ℝ) * (m : ℝ)^2 / ((m : ℝ)-1)^2 ≤ 17/32 := by
    apply (div_le_iff₀ (sq_pos_of_pos hd)).mpr
    nlinarith [sq_nonneg ((m : ℝ)-3)]
  have hsecond : (1/3 : ℝ) * ((m : ℝ)-3) / ((m : ℝ)-1) ≤ 1/3 := by
    apply (div_le_iff₀ hd).mpr
    linarith
  linarith

theorem induction_factor_seventeen_lt_one (m : ℕ) (hm : 3 ≤ m) :
    (34 / 144 : ℝ) * (m : ℝ)^2 / ((m : ℝ)-1)^2 +
      (1/3 : ℝ) * ((m : ℝ)-3) / ((m : ℝ)-1) < 1 := by
  have h := induction_factor_seventeen_le_eightyThree_ninetySixths m hm
  linarith

/-- The literal factor after paper (106), with the actual C=17. -/
theorem actual_induction_factor_seventeen_lt_one (m : ℕ) (hm : 3 ≤ m) :
    (2 * 17 / 144 : ℝ) * (m : ℝ)^2 / ((m : ℝ)-1)^2 +
      (4 / Real.sqrt 144) * ((m : ℝ)-3) / ((m : ℝ)-1) < 1 := by
  have hs : Real.sqrt 144 = 12 := by norm_num
  rw [hs]
  norm_num only
  convert induction_factor_seventeen_lt_one m hm using 1
  ring

/-- The remaining explicit parameter restrictions in the source induction. -/
theorem induction_parameter_144_side_conditions :
    (1 : ℝ) ≤ 144 ∧ (5 : ℝ) ≤ 144 ∧ (64 : ℝ) ≤ 144 := by norm_num

/-- Denominator-free form at tensor rank r=m-1, useful for the actual induction. -/
theorem induction_coefficient_seventeen_le (r : ℕ) (hr : 2 ≤ r) :
    34 * ((r : ℝ)+1)^2 + 48 * (r : ℝ) * ((r : ℝ)-2) ≤ 144 * (r : ℝ)^2 := by
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  nlinarith [sq_nonneg ((r : ℝ)-2)]

/-- One complete scalar energy step. Here Bprev=b_(m-1), B=b_m,
e is the integrated m-th energy, and l the integrated squared lower tensor. -/
theorem energy_induction_scalar_step (r : ℕ) (hr : 2 ≤ r)
    {Bprev B e l : ℝ} (hprev : 0 ≤ Bprev) (he0 : 0 ≤ e) (hl0 : 0 ≤ l)
    (hB : B = 144 * (r : ℝ)^2 * Bprev)
    (he : e ≤ 2 * Bprev) (hl : l ≤ 2 * ((r : ℝ)-2)^2 * B) :
    17 * ((r+1 : ℕ) : ℝ)^2 * e + 2 * Real.sqrt e * Real.sqrt l ≤ B := by
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hroot : Real.sqrt e * Real.sqrt l ≤ 24 * (r : ℝ) * ((r : ℝ)-2) * Bprev := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt he0, Real.sq_sqrt hl0]
    calc
      e*l ≤ (2*Bprev) * (2*((r : ℝ)-2)^2*B) :=
        mul_le_mul he hl hl0 (by positivity)
      _ = (24*(r : ℝ)*((r : ℝ)-2)*Bprev)^2 := by rw [hB]; ring
  have hmain := mul_le_mul_of_nonneg_left he (show 0 ≤ 17 * ((r+1 : ℕ) : ℝ)^2 by positivity)
  have hcoef := mul_le_mul_of_nonneg_right (induction_coefficient_seventeen_le r hr) hprev
  push_cast at hmain ⊢
  rw [hB]
  nlinarith

end KLS.RouteArithmetic
end
#print axioms KLS.RouteArithmetic.energy_induction_scalar_step
#print axioms KLS.RouteArithmetic.actual_induction_factor_seventeen_lt_one

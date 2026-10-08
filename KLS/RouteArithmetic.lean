import Mathlib

/-!
# Scalar arithmetic for a possible KLS proof route

This file proves arithmetic facts only.  It does not establish a Poincaré
inequality for any measure, nor a KLS theorem.  The parameter choices are
conditional extractions from the handwritten Bizeul–Klartag–Lehec route.
The analytic estimates to which the numbers would apply remain separate
proof obligations.
-/

namespace KLS.RouteArithmetic

/-- Conditional parameter extraction: the coefficient occurring in the
cumulant-energy drift estimate can be bounded by `16 * m^2`.
This statement contains no stochastic or measure-theoretic estimate. -/
theorem drift_coefficient_le (m : ℕ) (hm : 3 ≤ m) :
    (m : ℝ) + 1 + 16 * ((m : ℝ) - 1) ^ 2 ≤ 16 * (m : ℝ) ^ 2 := by
  have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
  nlinarith

/-- The real scalar induction factor with proposed cumulant parameter 144
is at most `5/6`, in particular strictly less than one. -/
theorem induction_factor_le_five_sixths (m : ℕ) (hm : 3 ≤ m) :
    (32 / 144 : ℝ) * (m : ℝ) ^ 2 / ((m : ℝ) - 1) ^ 2 +
      (1 / 3 : ℝ) * ((m : ℝ) - 3) / ((m : ℝ) - 1) ≤ 5 / 6 := by
  have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hd : 0 < (m : ℝ) - 1 := by linarith
  have hfirst : (32 / 144 : ℝ) * (m : ℝ) ^ 2 /
      ((m : ℝ) - 1) ^ 2 ≤ 1 / 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hd)).2
    nlinarith [sq_nonneg ((m : ℝ) - 3)]
  have hsecond : (1 / 3 : ℝ) * ((m : ℝ) - 3) /
      ((m : ℝ) - 1) ≤ 1 / 3 := by
    apply (div_le_iff₀ hd).2
    linarith
  linarith

theorem induction_factor_lt_one (m : ℕ) (hm : 3 ≤ m) :
    (32 / 144 : ℝ) * (m : ℝ) ^ 2 / ((m : ℝ) - 1) ^ 2 +
      (1 / 3 : ℝ) * ((m : ℝ) - 3) / ((m : ℝ) - 1) < 1 := by
  have h := induction_factor_le_five_sixths m hm
  linarith

private theorem nat_le_two_pow (q : ℕ) : q ≤ 2 ^ q := by
  induction q with
  | zero => norm_num
  | succ q ih =>
    have hp : 0 < 2 ^ q := by positivity
    calc
      q + 1 ≤ 2 * 2 ^ q := by omega
      _ = 2 ^ (q + 1) := by rw [pow_succ]; omega

/-- An elementary exponential bound for the scalar coefficient in a tensor
symmetrization estimate. It holds even at zero. -/
theorem symmetrization_coefficient_le (q : ℕ) : q ^ 4 * 2 ^ q ≤ 32 ^ q := by
  have hpower : (2 ^ q) ^ 4 = (2 ^ 4) ^ q := by
    simp only [← pow_mul, Nat.mul_comm q 4]
  calc
    q ^ 4 * 2 ^ q ≤ (2 ^ q) ^ 4 * 2 ^ q := by
      gcongr
      exact nat_le_two_pow q
    _ = (2 ^ 4) ^ q * 2 ^ q := by rw [hpower]
    _ = (2 ^ 4 * 2) ^ q := by rw [mul_pow]
    _ = 32 ^ q := by norm_num

/-- First of the two scalar coefficient bounds behind the conservative
proposed parameter `2^17` in the tilt-criterion calculation. -/
theorem tilt_main_coefficient_le (d : ℕ) (hd : 1 ≤ d) :
    2 * 32 ^ d ≤ 131072 ^ d := by
  have htwo : (2 : ℕ) ≤ 2 ^ d := by
    simpa using (pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) hd)
  calc
    2 * 32 ^ d ≤ 2 ^ d * 32 ^ d := Nat.mul_le_mul_right _ htwo
    _ = 64 ^ d := by rw [← mul_pow]; norm_num
    _ ≤ 131072 ^ d := by gcongr <;> norm_num

/-- Second scalar coefficient bound. It is an inequality of integers and
does not assert the analytic tensor estimate where it could be used. -/
theorem tilt_error_coefficient_le (d : ℕ) (hd : 1 ≤ d) :
    2 * (1 + 4 ^ d) ^ 2 * 32 ^ (2 * d) ≤ 131072 ^ d := by
  have hfour : 0 < 4 ^ d := by positivity
  have hsmall : 1 + 4 ^ d ≤ 2 * 4 ^ d := by omega
  have height : (8 : ℕ) ≤ 8 ^ d := by
    simpa using (pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 8) hd)
  have hswap : (4 ^ d) ^ 2 = (4 ^ 2) ^ d := by
    simp only [← pow_mul, Nat.mul_comm d 2]
  calc
    2 * (1 + 4 ^ d) ^ 2 * 32 ^ (2 * d) ≤
        2 * (2 * 4 ^ d) ^ 2 * 32 ^ (2 * d) := by gcongr
    _ = 8 * 16 ^ d * 1024 ^ d := by
      rw [mul_pow, hswap, pow_mul]
      norm_num
      ring
    _ = 8 * 16384 ^ d := by rw [mul_assoc, ← mul_pow]; norm_num
    _ ≤ 8 ^ d * 16384 ^ d := Nat.mul_le_mul_right _ height
    _ = 131072 ^ d := by rw [← mul_pow]; norm_num

/-- Numerical evaluation of a candidate bound. This is an equality of natural
numbers, not a bound on a Poincaré constant. -/
theorem candidate_bound_eval :
    (100 : ℕ) * (2 ^ 17) ^ 2 * 288 = 494780232499200 := by
  norm_num

/-- Scalar algebra for three proposed moment expressions.  No integral,
probability distribution, or moment identity is asserted here. -/
theorem exponential_moment_ratio_algebra (a : ℝ) (ha : 0 < a)
    (ha2 : a < 1 / 2) :
    (1 / (1 - 2 * a) - (1 / (1 - a)) ^ 2) /
      (a ^ 2 / (1 - 2 * a)) = 1 / (1 - a) ^ 2 := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have h1 : 1 - a ≠ 0 := by linarith
  have h2 : 1 - 2 * a ≠ 0 := by linarith
  field_simp [ha0, h1, h2]
  <;> ring

/-- Positivity of the proposed scalar energy expression. -/
theorem exponential_energy_expression_pos (a : ℝ) (ha : 0 < a)
    (ha2 : a < 1 / 2) : 0 < a ^ 2 / (1 - 2 * a) := by
  apply div_pos (sq_pos_of_pos ha)
  linarith

/-- The scalar ratios are below four before the limiting parameter. -/
theorem ratio_lt_four (a : ℝ) (ha : 0 < a) (ha2 : a < 1 / 2) :
    1 / (1 - a) ^ 2 < 4 := by
  have hd : 0 < 1 - a := by linarith
  apply (div_lt_iff₀ (sq_pos_of_pos hd)).2
  nlinarith [sq_nonneg (a - 1 / 2)]

/-- The scalar ratios approach four: every real upper bound for all of them
is at least four.  The hypothesis is purely algebraic, and does not assert
that these expressions have been realized by any probability measure. -/
theorem four_le_of_scalar_ratio_bounds (C : ℝ)
    (hC : ∀ a : ℝ, 0 < a → a < 1 / 2 → 1 / (1 - a) ^ 2 ≤ C) :
    4 ≤ C := by
  by_contra h
  have hlt : C < 4 := lt_of_not_ge h
  let t : ℝ := min (1 / 2) ((4 - C) / 16)
  have ht : 0 < t := by
    dsimp [t]
    apply lt_min
    · norm_num
    · linarith
  have ht_half : t ≤ 1 / 2 := min_le_left _ _
  have ht_small : t ≤ (4 - C) / 16 := min_le_right _ _
  let a : ℝ := (1 - t) / 2
  have ha : 0 < a := by dsimp [a]; linarith
  have ha2 : a < 1 / 2 := by dsimp [a]; linarith
  have ht1 : 0 < 1 + t := by linarith
  have hden : 0 < (1 + t) ^ 2 := sq_pos_of_pos ht1
  have hproduct : 0 ≤ t ^ 2 * (8 * t + 12) := by positivity
  have hlower : 4 - 8 * t ≤ 4 / (1 + t) ^ 2 := by
    apply (le_div_iff₀ hden).2
    nlinarith
  have hane : 1 - a ≠ 0 := by linarith
  have hratio : 1 / (1 - a) ^ 2 = 4 / (1 + t) ^ 2 := by
    field_simp [hane, ne_of_gt ht1]
    dsimp [a]
    ring
  have hupper := hC a ha ha2
  rw [hratio] at hupper
  linarith

end KLS.RouteArithmetic

#print axioms KLS.RouteArithmetic.drift_coefficient_le
#print axioms KLS.RouteArithmetic.induction_factor_le_five_sixths
#print axioms KLS.RouteArithmetic.induction_factor_lt_one
#print axioms KLS.RouteArithmetic.symmetrization_coefficient_le
#print axioms KLS.RouteArithmetic.tilt_main_coefficient_le
#print axioms KLS.RouteArithmetic.tilt_error_coefficient_le
#print axioms KLS.RouteArithmetic.candidate_bound_eval
#print axioms KLS.RouteArithmetic.exponential_moment_ratio_algebra
#print axioms KLS.RouteArithmetic.exponential_energy_expression_pos
#print axioms KLS.RouteArithmetic.ratio_lt_four
#print axioms KLS.RouteArithmetic.four_le_of_scalar_ratio_bounds

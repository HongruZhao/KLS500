import KLS.WeightedResolventPositivity

noncomputable section
namespace KLS.ConstantReduction

theorem profile_bernoulli {x : ℝ} (hx : 0 ≤ x) (m : ℕ) :
    1+(m : ℝ)*x ≤ (1+x)^m := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    have hh := mul_le_mul_of_nonneg_right ih (by positivity : 0 ≤ 1+x)
    have hp : 0 ≤ (m : ℝ)*x^2 := by positivity
    rw [pow_succ]
    push_cast
    nlinarith only [hh,hp]

/-- The number of steps can be made arbitrarily large while the spectral
contraction remains bounded by one fixed rational number. -/
theorem profile_block16_contraction (m : ℕ) (hm : 1 ≤ m) :
    ((16*(m : ℝ))/(16*(m : ℝ)+1))^(16*m) ≤ (19/50 : ℝ) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hden : (0 : ℝ) < 16*(m : ℝ) := by positivity
  have hden' : (0 : ℝ) < 16*(m : ℝ)+1 := by positivity
  let r : ℝ := (16*(m : ℝ))/(16*(m : ℝ)+1)
  let q : ℝ := 1+1/(16*(m : ℝ))
  have hb := profile_bernoulli (by positivity : 0 ≤ 1/(16*(m : ℝ))) m
  have hc : 1+(m : ℝ)*(1/(16*(m : ℝ))) = (17/16 : ℝ) := by
    field_simp
    ring
  rw [hc] at hb
  have hrq : r*q = 1 := by
    dsimp only [r,q]
    field_simp
  have heq : r^m*q^m = 1 := by rw [← mul_pow,hrq,one_pow]
  have hmul := mul_le_mul_of_nonneg_left hb (pow_nonneg (by positivity : 0 ≤ r) m)
  change r^m*(17/16 : ℝ) ≤ r^m*q^m at hmul
  rw [heq] at hmul
  have hr : r^m ≤ (16/17 : ℝ) := by nlinarith only [hmul]
  have hp := pow_le_pow_left₀ (pow_nonneg (by positivity : 0 ≤ r) m) hr 16
  have hn : (16/17 : ℝ)^16 ≤ (19/50 : ℝ) := by norm_num
  calc
    _ = (r^m)^16 := by dsimp only [r]; rw [← pow_mul,Nat.mul_comm m 16]
    _ ≤ (16/17 : ℝ)^16 := hp
    _ ≤ (19/50 : ℝ) := hn

/-- A deliberately loose scalar certificate leaves room for finite-prefix
and lag errors in the improved profile argument. -/
theorem profile_displacement_scalar_certificate :
    2*(101/100 : ℝ)*Real.sqrt ((2/3 : ℝ)*(101/100)/(19/10)) ≤ (1203/1000 : ℝ) := by
  have hs : 0 ≤ Real.sqrt ((2/3 : ℝ)*(101/100)/(19/10)) := Real.sqrt_nonneg _
  have he := Real.sq_sqrt (show (0 : ℝ) ≤ (2/3 : ℝ)*(101/100)/(19/10) by norm_num)
  nlinarith only [hs,he]

theorem profile_cheeger_scalar_certificate :
    (121/100 : ℝ)/(31/50) ≤ (49/25 : ℝ) := by norm_num

/-- At total time 5C/4, multiples of 128 steps give a uniform rational
spectral gap while leaving the step size arbitrarily small. -/
theorem profile_block128_contraction (m : ℕ) (hm : 1 ≤ m) :
    ((512*(m : ℝ))/(512*(m : ℝ)+5))^(128*m) ≤ (29/100 : ℝ) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hden : (0 : ℝ) < 512*(m : ℝ) := by positivity
  have hden' : (0 : ℝ) < 512*(m : ℝ)+5 := by positivity
  let r : ℝ := (512*(m : ℝ))/(512*(m : ℝ)+5)
  let q : ℝ := 1+5/(512*(m : ℝ))
  have hb := profile_bernoulli (by positivity : 0 ≤ 5/(512*(m : ℝ))) m
  have hc : 1+(m : ℝ)*(5/(512*(m : ℝ))) = (517/512 : ℝ) := by
    field_simp
    ring
  rw [hc] at hb
  have hrq : r*q = 1 := by
    dsimp only [r,q]
    field_simp
  have heq : r^m*q^m = 1 := by rw [← mul_pow,hrq,one_pow]
  have hmul := mul_le_mul_of_nonneg_left hb (pow_nonneg (by positivity : 0 ≤ r) m)
  change r^m*(517/512 : ℝ) ≤ r^m*q^m at hmul
  rw [heq] at hmul
  have hr : r^m ≤ (512/517 : ℝ) := by nlinarith only [hmul]
  have hp := pow_le_pow_left₀ (pow_nonneg (by positivity : 0 ≤ r) m) hr 128
  have hn : (512/517 : ℝ)^128 ≤ (29/100 : ℝ) := by norm_num
  calc
    _ = (r^m)^128 := by dsimp only [r]; rw [← pow_mul,Nat.mul_comm m 128]
    _ ≤ (512/517 : ℝ)^128 := hp
    _ ≤ (29/100 : ℝ) := hn

theorem polynomial_profile_displacement_scalar_certificate :
    2*(87/100 : ℝ)*Real.sqrt ((101/100 : ℝ)*(5/4)/(99/50)) ≤ (139/100 : ℝ) := by
  have hs := Real.sqrt_nonneg ((101/100 : ℝ)*(5/4)/(99/50))
  have he := Real.sq_sqrt (show (0 : ℝ) ≤ (101/100 : ℝ)*(5/4)/(99/50) by norm_num)
  nlinarith only [hs,he]

theorem polynomial_profile_cheeger_scalar_certificate :
    ((139/100 : ℝ)+1/200)/(71/100) ≤ (197/100 : ℝ) := by norm_num

end KLS.ConstantReduction
end

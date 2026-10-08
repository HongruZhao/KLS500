import SpectralReductionFirstImprovedSymmetrization

/-! Elementary bounds for the exact central-binomial coefficients. The low
rank d=1 values are retained, and only ranks d≥2 use polynomial majorants. -/

noncomputable section
namespace KLS.ConstantReduction

theorem twice_choose_le_four_pow {d : ℕ} (hd : 1 ≤ d) :
    2 * ((2 * d).choose d : ℝ) ≤ (4 : ℝ) ^ d := by
  have hc := Nat.choose_succ_le_two_pow (2 * d - 1) d
  rw [show 2 * d - 1 + 1 = 2 * d by omega] at hc
  have hr : ((2 * d).choose d : ℝ) ≤ (2 : ℝ) ^ (2 * d - 1) := by exact_mod_cast hc
  have hp : (2 : ℝ) ^ (2 * d - 1) * 2 = 4 ^ d := by
    rw [← pow_succ, show 2 * d - 1 + 1 = 2 * d by omega, pow_mul]
    norm_num
  linarith

theorem four_pow_ge_sixteen {d : ℕ} (hd : 2 ≤ d) :
    (16 : ℝ) ≤ (4 : ℝ) ^ d := by
  have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hd
  norm_num at hp
  exact hp

theorem exactTaylorMainCoefficient_le {d : ℕ} (hd : 1 ≤ d) :
    exactTaylorMainCoefficient d ≤ (32 : ℝ) ^ d := by
  have hc := twice_choose_le_four_pow hd
  have hcsq : 2 * ((2 * d).choose d : ℝ) ^ 2 ≤ (16 : ℝ) ^ d := by
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * ((2 * d).choose d : ℝ)) hc 2
    have he : ((4 : ℝ) ^ d) ^ 2 = (16 : ℝ) ^ d := by
      rw [← pow_mul, Nat.mul_comm d 2, pow_mul]; norm_num
    rw [he] at hp
    nlinarith [sq_nonneg (((2 * d).choose d : ℝ))]
  unfold exactTaylorMainCoefficient
  calc
    _ ≤ (16 : ℝ) ^ d * 2 ^ d := mul_le_mul_of_nonneg_right hcsq (by positivity)
    _ = (32 : ℝ) ^ d := by rw [← mul_pow]; norm_num

theorem exactTaylorErrorCoefficient_le_polynomial {d : ℕ} (hd : 2 ≤ d) :
    exactTaylorErrorCoefficient firstImprovedSymmetrizationCoefficient d ≤
      41 * (d : ℝ) ^ 4 * (64 : ℝ) ^ d := by
  have hc := twice_choose_le_four_pow (show 1 ≤ d by omega)
  have h4 := four_pow_ge_sixteen hd
  have hc1 : 1 + ((2 * d).choose d : ℝ) ≤ (9 / 16 : ℝ) * 4 ^ d := by linarith
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + ((2 * d).choose d : ℝ)) hc1 2
  have he4 : ((4 : ℝ) ^ d) ^ 2 = (16 : ℝ) ^ d := by
    rw [← pow_mul, Nat.mul_comm d 2, pow_mul]; norm_num
  have hc2 : 2 * (1 + ((2 * d).choose d : ℝ)) ^ 2 ≤
      (81 / 128 : ℝ) * 16 ^ d := by
    rw [mul_pow, he4] at hp
    nlinarith
  have hs : firstImprovedSymmetrizationCoefficient (2 * d) =
      64 * (d : ℝ) ^ 4 * 4 ^ d := by
    simp only [firstImprovedSymmetrizationCoefficient, show 2 * d ≠ 2 by omega, ↓reduceIte,
      Nat.cast_mul, Nat.cast_ofNat, pow_mul]
    norm_num
    ring
  have he : (16 : ℝ) ^ d * 4 ^ d = 64 ^ d := by rw [← mul_pow]; norm_num
  unfold exactTaylorErrorCoefficient
  rw [hs]
  calc
    _ ≤ ((81 / 128 : ℝ) * 16 ^ d) * (64 * (d : ℝ) ^ 4 * 4 ^ d) :=
      mul_le_mul_of_nonneg_right hc2 (by positivity)
    _ = (81 / 2 : ℝ) * (d : ℝ) ^ 4 * 64 ^ d := by rw [← he]; ring
    _ ≤ _ := by
      have hn : 0 ≤ (d : ℝ) ^ 4 * (64 : ℝ) ^ d := by positivity
      nlinarith

theorem exactTaylorMainCoefficient_one : exactTaylorMainCoefficient 1 = 16 := by
  norm_num [exactTaylorMainCoefficient]

theorem exactTaylorErrorCoefficient_one :
    exactTaylorErrorCoefficient firstImprovedSymmetrizationCoefficient 1 = 18 := by
  norm_num [exactTaylorErrorCoefficient, firstImprovedSymmetrizationCoefficient]

end KLS.ConstantReduction
end

#print axioms KLS.ConstantReduction.exactTaylorMainCoefficient_le
#print axioms KLS.ConstantReduction.exactTaylorErrorCoefficient_le_polynomial

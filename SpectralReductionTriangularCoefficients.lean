import SpectralReductionPolynomialBounds
import SpectralReductionRankTaylorTwentyNine

/-! The coefficient sequence for exact two-slot averaging and triangular
adjacent-permutation words. Its actual-iteration estimate is supplied in the
separate analytic bridge; this file proves only numerical bounds. -/

noncomputable section
namespace KLS.ConstantReduction

def triangularSymmetrizationCoefficient (m : ℕ) : ℝ :=
  if m = 2 then 1 else ((m : ℝ) - 1) ^ 2 * (m : ℝ) ^ 2 * 2 ^ m / 8

theorem triangularSymmetrizationCoefficient_nonneg (m : ℕ) :
    0 ≤ triangularSymmetrizationCoefficient m := by
  unfold triangularSymmetrizationCoefficient
  split <;> positivity

theorem triangularSymmetrizationCoefficient_le {d : ℕ} (hd : 2 ≤ d) :
    triangularSymmetrizationCoefficient (2 * d) ≤ 2 * (d : ℝ) ^ 4 * 4 ^ d := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : 0 ≤ 2 * (d : ℝ) - 1 := by linarith
  have hsq := pow_le_pow_left₀ hd0 (show 2 * (d : ℝ) - 1 ≤ 2 * (d : ℝ) by linarith) 2
  have hp := mul_le_mul_of_nonneg_right hsq
    (show 0 ≤ (2 * (d : ℝ)) ^ 2 * (4 : ℝ) ^ d / 8 by positivity)
  simp only [triangularSymmetrizationCoefficient, show 2 * d ≠ 2 by omega, ↓reduceIte,
    Nat.cast_mul, Nat.cast_ofNat, pow_mul]
  norm_num
  nlinarith

theorem exactTaylorErrorCoefficient_le_triangular {d : ℕ} (hd : 2 ≤ d) :
    exactTaylorErrorCoefficient triangularSymmetrizationCoefficient d ≤
      (81 / 64 : ℝ) * (d : ℝ) ^ 4 * 64 ^ d := by
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
  have he : (16 : ℝ) ^ d * 4 ^ d = 64 ^ d := by rw [← mul_pow]; norm_num
  unfold exactTaylorErrorCoefficient
  calc
    _ ≤ ((81 / 128 : ℝ) * 16 ^ d) * (2 * (d : ℝ) ^ 4 * 4 ^ d) :=
      mul_le_mul hc2 (triangularSymmetrizationCoefficient_le hd)
        (triangularSymmetrizationCoefficient_nonneg _) (by positivity)
    _ = _ := by rw [← he]; ring

theorem one_add_exactTaylorErrorCoefficient_le_triangular {d : ℕ} (hd : 2 ≤ d) :
    1 + exactTaylorErrorCoefficient triangularSymmetrizationCoefficient d ≤
      (3 / 2 : ℝ) * (d : ℝ) ^ 4 * 64 ^ d := by
  have hh := exactTaylorErrorCoefficient_le_triangular hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hd4 : (1 : ℝ) ≤ (d : ℝ) ^ 4 := one_le_pow₀ hd1
  have hp : (64 : ℝ) ≤ (64 : ℝ) ^ d := by
    have hp' := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 64) (show 1 ≤ d by omega)
    simpa using hp'
  have hprod := mul_le_mul_of_nonneg_right hd4 (by positivity : 0 ≤ (64 : ℝ) ^ d)
  nlinarith

def rankDyadicMain (d : ℕ) : ℝ := exactTaylorMainCoefficient d / 32 ^ d

def rankDyadicError (d : ℕ) : ℝ :=
  32 ^ (d - 1) * ((2 * d - 1 : ℕ) : ℝ) *
    (1 + exactTaylorErrorCoefficient triangularSymmetrizationCoefficient d) *
      improvedTaylorCoefficientTwentyNine d

theorem rankDyadicMain_nonneg (d : ℕ) : 0 ≤ rankDyadicMain d := by
  unfold rankDyadicMain exactTaylorMainCoefficient
  positivity

theorem rankDyadicMain_le_one {d : ℕ} (hd : 1 ≤ d) : rankDyadicMain d ≤ 1 := by
  unfold rankDyadicMain
  exact (div_le_one (by positivity)).mpr (exactTaylorMainCoefficient_le hd)

theorem rankDyadicError_nonneg (d : ℕ) : 0 ≤ rankDyadicError d := by
  have hσ := triangularSymmetrizationCoefficient_nonneg (2 * d)
  have hβ := improvedTaylorCoefficientTwentyNine_nonneg d
  unfold rankDyadicError exactTaylorErrorCoefficient
  positivity

end KLS.ConstantReduction
end

#print axioms KLS.ConstantReduction.one_add_exactTaylorErrorCoefficient_le_triangular

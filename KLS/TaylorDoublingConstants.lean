import KLS.FiniteAveragePerturbation

/-! One explicit universal constant absorbs both coefficients in the actual
Taylor doubling estimate. No optimization of this constant is intended. -/

noncomputable section
namespace KLS

def bklTaylorDoublingConstant : ℝ := 2097152

theorem one_le_bklTaylorDoublingConstant : 1 ≤ bklTaylorDoublingConstant := by
  norm_num [bklTaylorDoublingConstant]

theorem taylorDoubling_main_coefficient {d : ℕ} (hd : 1 ≤ d) {lam : ℝ} (hlam : 0 ≤ lam) :
    2 * (16 : ℝ) ^ d * (2 * lam) ^ d ≤ (bklTaylorDoublingConstant * lam) ^ d := by
  have h2 : (2 : ℝ) ≤ 2 ^ d := le_self_pow₀ (by norm_num) (by omega)
  have hbase : 2 * (16 : ℝ) ^ d * 2 ^ d ≤ bklTaylorDoublingConstant ^ d := by
    calc
      _ ≤ (2 : ℝ) ^ d * 16 ^ d * 2 ^ d :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 (by positivity)) (by positivity)
      _ = (64 : ℝ) ^ d := by rw [← mul_pow, ← mul_pow]; norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) (by norm_num [bklTaylorDoublingConstant]) d
  calc
    _ = (2 * (16 : ℝ) ^ d * 2 ^ d) * lam ^ d := by rw [mul_pow]; ring
    _ ≤ bklTaylorDoublingConstant ^ d * lam ^ d :=
      mul_le_mul_of_nonneg_right hbase (pow_nonneg hlam d)
    _ = _ := (mul_pow _ _ _).symm

theorem taylorDoubling_error_coefficient {d : ℕ} (hd : 1 ≤ d) :
    8 * (16 : ℝ) ^ d * (128 : ℝ) ^ (2 * d) ≤ bklTaylorDoublingConstant ^ d := by
  have h8 : (8 : ℝ) ≤ 8 ^ d := le_self_pow₀ (by norm_num) (by omega)
  calc
    _ = 8 * (262144 : ℝ) ^ d := by
      rw [pow_mul]
      norm_num
      rw [mul_assoc, ← mul_pow]
      norm_num
    _ ≤ (8 : ℝ) ^ d * 262144 ^ d := mul_le_mul_of_nonneg_right h8 (by positivity)
    _ = _ := by rw [← mul_pow]; norm_num [bklTaylorDoublingConstant]

end KLS
end

#print axioms KLS.taylorDoubling_main_coefficient
#print axioms KLS.taylorDoubling_error_coefficient

import KLS.DyadicSpectralArithmetic

/-! Scalar consequence of the summed actual-Taylor recurrence. The analytic
recurrence and mean-loss inequality remain explicit inputs here. -/
noncomputable section
namespace KLS

theorem spectral_recurrence_scaled
    {C lam R : ℝ} (hC : 1 ≤ C) (hlam : 0 < lam)
    (hsmall : C ^ 2 * lam * R ^ 2 ≤ 1 / 100)
    (S : ℕ → ℝ)
    (hrec : ∀ d, 1 ≤ d → S d ≤ (C * lam) ^ d * S (2 * d) +
      4 * (d : ℝ) * C ^ d * lam * R ^ (2 * d))
    {d : ℕ} (hd : 1 ≤ d) :
    (C * lam) ^ (d - 1) * S d ≤
      (C * lam) ^ (2 * d - 1) * S (2 * d) +
        4 * (d : ℝ) * (1 / 100 : ℝ) ^ d := by
  have hC0 : 0 ≤ C := by linarith
  have hA : 0 ≤ C * lam := mul_nonneg hC0 hlam.le
  have hp := mul_le_mul_of_nonneg_left (hrec d hd) (pow_nonneg hA (d - 1))
  have hmain : (C * lam) ^ (d - 1) * (C * lam) ^ d =
      (C * lam) ^ (2 * d - 1) := by
    rw [← pow_add, show d - 1 + d = 2 * d - 1 by omega]
  have hlamPow : lam ^ (d - 1) * lam = lam ^ d := by
    rw [← pow_succ, show d - 1 + 1 = d by omega]
  have hCpow : C ^ (d - 1) ≤ C ^ d := pow_le_pow_right₀ hC (by omega)
  have herr : (C * lam) ^ (d - 1) *
      (4 * (d : ℝ) * C ^ d * lam * R ^ (2 * d)) ≤
      4 * (d : ℝ) * (1 / 100 : ℝ) ^ d := by
    have hid : (C * lam) ^ (d - 1) *
        (4 * (d : ℝ) * C ^ d * lam * R ^ (2 * d)) =
        4 * (d : ℝ) * (C ^ (d - 1) * C ^ d) * lam ^ d * (R ^ 2) ^ d := by
      rw [mul_pow, pow_mul]
      calc
        _ = 4 * (d : ℝ) * (C ^ (d - 1) * C ^ d) *
            (lam ^ (d - 1) * lam) * (R ^ 2) ^ d := by ring
        _ = _ := by rw [hlamPow]
    rw [hid]
    calc
      _ ≤ 4 * (d : ℝ) * (C ^ d * C ^ d) * lam ^ d * (R ^ 2) ^ d := by
        gcongr
      _ = 4 * (d : ℝ) * (C ^ 2 * lam * R ^ 2) ^ d := by
        have hCp : (C ^ 2) ^ d = C ^ d * C ^ d := by
          rw [← pow_mul, Nat.mul_comm 2 d, pow_mul, pow_two]
        rw [mul_pow, mul_pow, hCp]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hsmall d) (by positivity)
  rw [mul_add, ← mul_assoc _ ((C * lam) ^ d), hmain] at hp
  exact hp.trans (by linarith [herr])

theorem spectral_sum_first_lt
    {C lam R : ℝ} (hC : 1 ≤ C) (hlam : 0 < lam)
    (hsmall : C ^ 2 * lam * R ^ 2 ≤ 1 / 100)
    (S : ℕ → ℝ) (N : ℕ) (hzero : ∀ d, N ≤ d → S d = 0)
    (hrec : ∀ d, 1 ≤ d → S d ≤ (C * lam) ^ d * S (2 * d) +
      4 * (d : ℝ) * C ^ d * lam * R ^ (2 * d)) :
    S 1 < 1 / 20 := by
  let T : ℕ → ℝ := fun d => (C * lam) ^ (d - 1) * S d
  have hz : ∀ d, N ≤ d → T d = 0 := by
    intro d hd
    simp [T, hzero d hd]
  have hs : ∀ d, 1 ≤ d → T d ≤ T (2 * d) + 4 * (d : ℝ) * (1 / 100 : ℝ) ^ d := by
    intro d hd
    exact spectral_recurrence_scaled hC hlam hsmall S hrec hd
  simpa [T] using dyadic_recurrence_first_lt T N hz hs

/-- Once the actual summed recurrence and actual mean-loss crossing have
been supplied, the positive spectral parameter exceeds the stated threshold. -/
theorem spectral_scalar_lower_bound
    {C lam R : ℝ} (hC : 1 ≤ C) (hlam : 0 < lam) (hR : 1 ≤ R)
    (S : ℕ → ℝ) (N : ℕ) (hzero : ∀ d, N ≤ d → S d = 0)
    (hrec : ∀ d, 1 ≤ d → S d ≤ (C * lam) ^ d * S (2 * d) +
      4 * (d : ℝ) * C ^ d * lam * R ^ (2 * d))
    (hmean : lam / 2 < lam ^ 2 + 2 * lam * S 1) :
    1 / (100 * C ^ 2) < lam * R ^ 2 := by
  by_contra hn
  have hC0 : 0 < C := by linarith
  have hsmall0 : lam * R ^ 2 ≤ 1 / (100 * C ^ 2) := le_of_not_gt hn
  have hsmall : C ^ 2 * lam * R ^ 2 ≤ 1 / 100 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 100 * C ^ 2)).mp hsmall0
    nlinarith
  have hs := spectral_sum_first_lt hC hlam hsmall S N hzero hrec
  have hRsq : 1 ≤ R ^ 2 := by nlinarith
  have hCsq : 1 ≤ C ^ 2 := by nlinarith
  have hprod : lam ≤ C ^ 2 * lam * R ^ 2 := by
    have h1 : lam ≤ lam * R ^ 2 := by nlinarith
    have h2 : lam * R ^ 2 ≤ C ^ 2 * (lam * R ^ 2) := by nlinarith
    nlinarith
  have hlamsmall : lam ≤ 1 / 100 := hprod.trans hsmall
  have hsProd : 2 * lam * S 1 < lam / 10 := by nlinarith
  have hlamSq : lam ^ 2 ≤ lam / 100 := by nlinarith
  nlinarith

end KLS
end

#print axioms KLS.spectral_scalar_lower_bound

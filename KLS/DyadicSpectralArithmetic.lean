import Mathlib

/-! Finite dyadic arithmetic for the spectral criterion. No measure, operator,
or Taylor estimate is assumed to satisfy these hypotheses in this module. -/
noncomputable section
namespace KLS

theorem degree_le_ten_pow_pred {d : ℕ} (hd : 1 ≤ d) :
    (d : ℝ) ≤ (10 : ℝ) ^ (d - 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  clear hd
  simp only [Nat.add_one_sub_one]
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [pow_succ]
    push_cast at *
    nlinarith [one_le_pow₀ (n := m) (by norm_num : (1 : ℝ) ≤ 10)]

def dyadicSpectralTail (d : ℕ) : ℝ := (1 / 20) * (1 / 10) ^ (d - 1)

theorem dyadicSpectralTail_pos (d : ℕ) : 0 < dyadicSpectralTail d := by
  unfold dyadicSpectralTail
  positivity

theorem dyadic_error_le {d : ℕ} (hd : 1 ≤ d) :
    4 * (d : ℝ) * (1 / 100 : ℝ) ^ d ≤
      (1 / 25 : ℝ) * (1 / 10 : ℝ) ^ (d - 1) := by
  have hpred : d = (d - 1) + 1 := by omega
  have hpow100 : (1 / 100 : ℝ) ^ d = (1 / 100 : ℝ) ^ (d - 1) * (1 / 100) := by
    conv_lhs => rw [hpred, pow_succ]
  calc
    _ = (1 / 25 : ℝ) * ((d : ℝ) * (1 / 100 : ℝ) ^ (d - 1)) := by
      rw [hpow100]
      ring
    _ ≤ (1 / 25 : ℝ) * ((10 : ℝ) ^ (d - 1) * (1 / 100 : ℝ) ^ (d - 1)) := by
      gcongr
      exact degree_le_ten_pow_pred hd
    _ = _ := by rw [← mul_pow]; norm_num

theorem dyadicSpectralTail_step {d : ℕ} (hd : 1 ≤ d) :
    dyadicSpectralTail (2 * d) + 4 * (d : ℝ) * (1 / 100 : ℝ) ^ d <
      dyadicSpectralTail d := by
  have hpow : (1 / 10 : ℝ) ^ d ≤ 1 / 10 := by
    simpa using pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 10)
      (by norm_num : (1 / 10 : ℝ) ≤ 1) hd
  have hexp : 2 * d - 1 = (d - 1) + d := by omega
  have htail : dyadicSpectralTail (2 * d) ≤
      (1 / 200 : ℝ) * (1 / 10 : ℝ) ^ (d - 1) := by
    unfold dyadicSpectralTail
    rw [hexp, pow_add]
    nlinarith [mul_le_mul_of_nonneg_left hpow
      (show 0 ≤ (1 / 10 : ℝ) ^ (d - 1) by positivity)]
  have he := dyadic_error_le hd
  have hp : 0 < (1 / 10 : ℝ) ^ (d - 1) := by positivity
  unfold dyadicSpectralTail at htail ⊢
  linarith

/-- A finitely supported sequence satisfying the scaled doubling inequality
has first value strictly below one twentieth. The proof uses a decreasing
geometric tail and a finite dyadic descent, with no infinite series. -/
theorem dyadic_recurrence_first_lt (T : ℕ → ℝ) (N : ℕ)
    (hzero : ∀ d, N ≤ d → T d = 0)
    (hstep : ∀ d, 1 ≤ d → T d ≤ T (2 * d) + 4 * (d : ℝ) * (1 / 100 : ℝ) ^ d) :
    T 1 < 1 / 20 := by
  have hdesc (m : ℕ) : ∀ d : ℕ, 1 ≤ d → N ≤ d * 2 ^ m →
      T d < dyadicSpectralTail d := by
    induction m with
    | zero =>
      intro d hd hN
      simp only [pow_zero, mul_one] at hN
      rw [hzero d hN]
      exact dyadicSpectralTail_pos d
    | succ m ih =>
      intro d hd hN
      have hN' : N ≤ (2 * d) * 2 ^ m := by
        simpa only [pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hN
      have hnext := ih (2 * d) (by omega) hN'
      have hinc : T (2 * d) + 4 * (d : ℝ) * (1 / 100 : ℝ) ^ d <
          dyadicSpectralTail (2 * d) + 4 * (d : ℝ) * (1 / 100 : ℝ) ^ d := by linarith
      exact (hstep d hd).trans_lt (hinc.trans (dyadicSpectralTail_step hd))
  have hN : N ≤ 1 * 2 ^ N := by
    simpa using (Nat.lt_two_pow_self (n := N)).le
  simpa [dyadicSpectralTail] using hdesc N 1 (by omega) hN

end KLS
end

#print axioms KLS.dyadic_recurrence_first_lt

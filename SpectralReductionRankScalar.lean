import SpectralReductionTriangularCoefficients

/-! Exact small-rank arithmetic and a finite dyadic tail for the actual
rank-sensitive BKL recurrence. The final numerical bound is 75000. -/

noncomputable section
namespace KLS.ConstantReduction

/-- Scaling keeps every exact central-binomial recurrence coefficient. -/
theorem rank_spectral_recurrence_scaled
    {lam : ℝ} (hlam : 0 < lam) (S : ℕ → ℝ)
    (hrec : ∀ d, 1 ≤ d → S d ≤ exactTaylorMainCoefficient d * lam ^ d * S (2 * d) +
      ((2 * d - 1 : ℕ) : ℝ) * (1 + exactTaylorErrorCoefficient triangularSymmetrizationCoefficient d) *
        lam * improvedTaylorCoefficientTwentyNine d)
    {d : ℕ} (hd : 1 ≤ d) :
    (32 * lam) ^ (d - 1) * S d ≤
      rankDyadicMain d * ((32 * lam) ^ (2 * d - 1) * S (2 * d)) + rankDyadicError d * lam ^ d := by
  have hp := mul_le_mul_of_nonneg_left (hrec d hd)
    (pow_nonneg (by positivity : 0 ≤ 32 * lam) (d - 1))
  have hmain : (32 * lam) ^ (d - 1) * (exactTaylorMainCoefficient d * lam ^ d) =
      rankDyadicMain d * (32 * lam) ^ (2 * d - 1) := by
    unfold rankDyadicMain
    rw [show 2 * d - 1 = (d - 1) + d by omega, pow_add]
    simp only [mul_pow]
    field_simp
    <;> ring
  have hlamPow : lam ^ (d - 1) * lam = lam ^ d := by
    rw [← pow_succ, show d - 1 + 1 = d by omega]
  have herr : (32 * lam) ^ (d - 1) *
      (((2 * d - 1 : ℕ) : ℝ) * (1 + exactTaylorErrorCoefficient triangularSymmetrizationCoefficient d) *
        lam * improvedTaylorCoefficientTwentyNine d) = rankDyadicError d * lam ^ d := by
    rw [mul_pow]
    calc
      _ = 32 ^ (d - 1) * ((2 * d - 1 : ℕ) : ℝ) *
          (1 + exactTaylorErrorCoefficient triangularSymmetrizationCoefficient d) *
          improvedTaylorCoefficientTwentyNine d * (lam ^ (d - 1) * lam) := by ring
      _ = _ := by rw [hlamPow]; rfl
  rw [mul_add, ← mul_assoc _ (exactTaylorMainCoefficient d * lam ^ d), hmain, herr] at hp
  simpa only [mul_assoc] using hp

theorem rankDyadicMain_small_bounds :
    rankDyadicMain 1 ≤ 1 / 2 ∧ rankDyadicMain 2 ≤ 9 / 32 ∧
      rankDyadicMain 4 ≤ 3 / 20 ∧ rankDyadicMain 8 ≤ 2 / 25 ∧ rankDyadicMain 16 ≤ 1 / 25 := by
  norm_num [rankDyadicMain, exactTaylorMainCoefficient, Nat.choose]

theorem rankDyadicError_small_bounds :
    rankDyadicError 1 * (1 / 75000 : ℝ) ^ 1 ≤ 1 / 3000 ∧
    rankDyadicError 2 * (1 / 75000 : ℝ) ^ 2 ≤ 1 / 1000 ∧
    rankDyadicError 4 * (1 / 75000 : ℝ) ^ 4 ≤ 84 / 125 ∧
    rankDyadicError 8 * (1 / 75000 : ℝ) ^ 8 ≤ 429 / 100 ∧
    rankDyadicError 16 * (1 / 75000 : ℝ) ^ 16 ≤ 213 / 20 := by
  norm_num [rankDyadicError, exactTaylorErrorCoefficient, triangularSymmetrizationCoefficient,
    improvedTaylorCoefficientTwentyNine, twentyNineRankWeight, Nat.choose]

theorem rankDyadicError_tail_bound {d : ℕ} (hd : 4 ≤ d) :
    rankDyadicError d * (1 / 75000 : ℝ) ^ d ≤
      (39 / 3200 : ℝ) * (d : ℝ) ^ 5 * (4 / 5 : ℝ) ^ d := by
  have hq : ((2 * d - 1 : ℕ) : ℝ) ≤ 2 * (d : ℝ) := by exact_mod_cast Nat.sub_le (2 * d) 1
  have he := one_add_exactTaylorErrorCoefficient_le_triangular (show 2 ≤ d by omega)
  have hβ := improvedTaylorCoefficientTwentyNine_le hd
  have hβ0 := improvedTaylorCoefficientTwentyNine_nonneg d
  have hσ0 := triangularSymmetrizationCoefficient_nonneg (2 * d)
  have he0 : 0 ≤ 1 + exactTaylorErrorCoefficient triangularSymmetrizationCoefficient d := by
    unfold exactTaylorErrorCoefficient
    positivity
  have hbound : rankDyadicError d * (1 / 75000 : ℝ) ^ d ≤
      32 ^ (d - 1) * (2 * (d : ℝ)) * ((3 / 2 : ℝ) * (d : ℝ) ^ 4 * 64 ^ d) *
        ((13 / 100 : ℝ) * 29 ^ d) * (1 / 75000 : ℝ) ^ d := by
    unfold rankDyadicError
    gcongr
  have hApow : (32 : ℝ) ^ (d - 1) = 32 ^ d / 32 := by
    have hh : (32 : ℝ) ^ (d - 1) * 32 = 32 ^ d := by
      rw [← pow_succ, show d - 1 + 1 = d by omega]
    linarith
  have hid : (32 : ℝ) ^ d * 64 ^ d * 29 ^ d * (1 / 75000 : ℝ) ^ d =
      (59392 / 75000 : ℝ) ^ d := by
    rw [← mul_pow, ← mul_pow, ← mul_pow]
    norm_num
  have hform : 32 ^ (d - 1) * (2 * (d : ℝ)) * ((3 / 2 : ℝ) * (d : ℝ) ^ 4 * 64 ^ d) *
        ((13 / 100 : ℝ) * 29 ^ d) * (1 / 75000 : ℝ) ^ d =
      (39 / 3200 : ℝ) * (d : ℝ) ^ 5 * (59392 / 75000 : ℝ) ^ d := by
    rw [hApow, ← hid]
    ring
  rw [hform] at hbound
  exact hbound.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 59392 / 75000) (by norm_num :
      (59392 / 75000 : ℝ) ≤ 4 / 5) d) (by positivity))

def rankDyadicTail (d : ℕ) : ℝ := (1 / 64) * (d : ℝ) ^ 5 * (4 / 5) ^ d

theorem rankDyadicTail_pos {d : ℕ} (hd : 32 ≤ d) : 0 < rankDyadicTail d := by
  have hd0 : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  unfold rankDyadicTail
  positivity

theorem rankDyadicTail_step {d : ℕ} (hd : 32 ≤ d) :
    rankDyadicTail (2 * d) + (39 / 3200 : ℝ) * (d : ℝ) ^ 5 * (4 / 5 : ℝ) ^ d ≤ rankDyadicTail d := by
  have hq : (4 / 5 : ℝ) ^ d ≤ 1 / 1024 := by
    have hh := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 4 / 5)
      (by norm_num : (4 / 5 : ℝ) ≤ 1) hd
    have hb : (4 / 5 : ℝ) ^ 32 ≤ 1 / 1024 := by norm_num
    exact hh.trans hb
  have hid : rankDyadicTail (2 * d) =
      (1 / 2 : ℝ) * (d : ℝ) ^ 5 * ((4 / 5 : ℝ) ^ d) ^ 2 := by
    unfold rankDyadicTail
    rw [Nat.cast_mul, Nat.cast_ofNat, Nat.mul_comm 2 d, pow_mul]
    ring
  have hm := mul_le_mul_of_nonneg_left hq
    (show 0 ≤ (1 / 2 : ℝ) * (d : ℝ) ^ 5 * (4 / 5 : ℝ) ^ d by positivity)
  rw [hid]
  unfold rankDyadicTail
  have hn : 0 ≤ (d : ℝ) ^ 5 * (4 / 5 : ℝ) ^ d := by positivity
  nlinarith

theorem rankDyadicTail_thirtyTwo : rankDyadicTail 32 < 416 := by
  norm_num [rankDyadicTail]

theorem rank_dyadic_recurrence_tail_lt (T : ℕ → ℝ) (hT : ∀ d, 0 ≤ T d) (N : ℕ)
    (hzero : ∀ d, N ≤ d → T d = 0)
    (hstep : ∀ d, 1 ≤ d → T d ≤ rankDyadicMain d * T (2 * d) + rankDyadicError d * (1 / 75000 : ℝ) ^ d) :
    T 32 < 416 := by
  have hs : ∀ d, 32 ≤ d → T d ≤ T (2 * d) + (39 / 3200 : ℝ) * (d : ℝ) ^ 5 * (4 / 5 : ℝ) ^ d := by
    intro d hd
    exact (hstep d (by omega)).trans (add_le_add
      (by simpa using mul_le_mul_of_nonneg_right (rankDyadicMain_le_one (show 1 ≤ d by omega)) (hT _))
      (rankDyadicError_tail_bound (by omega)))
  have hdesc (m : ℕ) : ∀ d : ℕ, 32 ≤ d → N ≤ d * 2 ^ m → T d < rankDyadicTail d := by
    induction m with
    | zero =>
      intro d hd hN
      simp only [pow_zero, mul_one] at hN
      rw [hzero d hN]
      exact rankDyadicTail_pos hd
    | succ m ih =>
      intro d hd hN
      have hN' : N ≤ (2 * d) * 2 ^ m := by
        simpa only [pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hN
      have hnext := ih (2 * d) (by omega) hN'
      have hinc : T (2 * d) + (39 / 3200 : ℝ) * (d : ℝ) ^ 5 * (4 / 5 : ℝ) ^ d <
          rankDyadicTail (2 * d) + (39 / 3200 : ℝ) * (d : ℝ) ^ 5 * (4 / 5 : ℝ) ^ d := by linarith
      exact (hs d hd).trans_lt (hinc.trans_le (rankDyadicTail_step hd))
  have hN : N ≤ 32 * 2 ^ N := by have hh := (Nat.lt_two_pow_self (n := N)).le; omega
  exact (hdesc N 32 (by omega) hN).trans rankDyadicTail_thirtyTwo

theorem rank_dyadic_recurrence_first_lt (T : ℕ → ℝ) (hT : ∀ d, 0 ≤ T d) (N : ℕ)
    (hzero : ∀ d, N ≤ d → T d = 0)
    (hstep : ∀ d, 1 ≤ d → T d ≤ rankDyadicMain d * T (2 * d) + rankDyadicError d * (1 / 75000 : ℝ) ^ d) :
    T 1 < 15 / 64 := by
  obtain ⟨hm1, hm2, hm4, hm8, hm16⟩ := rankDyadicMain_small_bounds
  obtain ⟨he1, he2, he4, he8, he16⟩ := rankDyadicError_small_bounds
  have h1 := (hstep 1 (by omega)).trans (add_le_add (mul_le_mul_of_nonneg_right hm1 (hT _)) he1)
  have h2 := (hstep 2 (by omega)).trans (add_le_add (mul_le_mul_of_nonneg_right hm2 (hT _)) he2)
  have h4 := (hstep 4 (by omega)).trans (add_le_add (mul_le_mul_of_nonneg_right hm4 (hT _)) he4)
  have h8 := (hstep 8 (by omega)).trans (add_le_add (mul_le_mul_of_nonneg_right hm8 (hT _)) he8)
  have h16 := (hstep 16 (by omega)).trans (add_le_add (mul_le_mul_of_nonneg_right hm16 (hT _)) he16)
  have h32 := rank_dyadic_recurrence_tail_lt T hT N hzero hstep
  norm_num only [Nat.mul_one, Nat.reduceMul] at h1 h2 h4 h8 h16
  linarith

theorem rank_spectral_scalar_lower_bound
    {lam : ℝ} (hlam : 0 < lam) (S : ℕ → ℝ) (hS : ∀ d, 0 ≤ S d) (N : ℕ)
    (hzero : ∀ d, N ≤ d → S d = 0)
    (hrec : ∀ d, 1 ≤ d → S d ≤ exactTaylorMainCoefficient d * lam ^ d * S (2 * d) +
      ((2 * d - 1 : ℕ) : ℝ) * (1 + exactTaylorErrorCoefficient triangularSymmetrizationCoefficient d) *
        lam * improvedTaylorCoefficientTwentyNine d)
    (hmean : lam / 2 < lam ^ 2 + 2 * lam * S 1) :
    1 / 75000 < lam := by
  by_contra hn
  have hsmall : lam ≤ 1 / 75000 := le_of_not_gt hn
  let T : ℕ → ℝ := fun d => (32 * lam) ^ (d - 1) * S d
  have hT : ∀ d, 0 ≤ T d := fun d => mul_nonneg (by positivity) (hS d)
  have hz : ∀ d, N ≤ d → T d = 0 := by intro d hd; simp [T, hzero d hd]
  have hs : ∀ d, 1 ≤ d → T d ≤ rankDyadicMain d * T (2 * d) + rankDyadicError d * (1 / 75000 : ℝ) ^ d := by
    intro d hd
    exact (rank_spectral_recurrence_scaled hlam S hrec hd).trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlam.le hsmall d) (rankDyadicError_nonneg d)))
  have hS1 : S 1 < 15 / 64 := by
    simpa [T] using rank_dyadic_recurrence_first_lt T hT N hz hs
  have hlamsmall : lam ≤ 1 / 32 := by linarith
  have hlamSq : lam ^ 2 ≤ lam / 32 := by nlinarith
  have hsProd : 2 * lam * S 1 < 15 * lam / 32 := by nlinarith
  nlinarith

end KLS.ConstantReduction
end

#print axioms KLS.ConstantReduction.rank_dyadic_recurrence_first_lt
#print axioms KLS.ConstantReduction.rank_spectral_scalar_lower_bound

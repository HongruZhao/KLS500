import KLS.WeightedResolventVariance

noncomputable section
namespace KLS.ConstantReduction

def entropyClock : ℕ → ℝ
  | 0 => 0
  | k+1 => (entropyClock k+Real.sqrt ((entropyClock k)^2+4))/2

theorem entropyClock_nonneg (k : ℕ) : 0 ≤ entropyClock k := by
  induction k with
  | zero => norm_num [entropyClock]
  | succ k ih => exact div_nonneg (add_nonneg ih (Real.sqrt_nonneg _)) (by norm_num)

theorem entropyClock_succ_ge_one (k : ℕ) : 1 ≤ entropyClock (k+1) := by
  have hs : (2 : ℝ) ≤ Real.sqrt ((entropyClock k)^2+4) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith [sq_nonneg (entropyClock k)]
  simp only [entropyClock]
  linarith [entropyClock_nonneg k]

theorem entropyClock_succ_equation (k : ℕ) :
    (entropyClock (k+1))^2-entropyClock k*entropyClock (k+1)=1 := by
  have hs := Real.sq_sqrt (show 0 ≤ (entropyClock k)^2+4 by positivity)
  simp only [entropyClock]
  nlinarith only [hs]

theorem entropyClock_square_increment_identity (k : ℕ) :
    (entropyClock (k+1))^2*((entropyClock (k+1))^2-(entropyClock k)^2) =
      2*(entropyClock (k+1))^2-1 := by
  have h := entropyClock_succ_equation k
  have hh := congrArg (fun a : ℝ => a^2) h
  nlinarith only [hh, congrArg (fun a : ℝ => 2*a) h,
    congrArg (fun a : ℝ => a*((entropyClock (k+1))^2+entropyClock k*entropyClock (k+1))) h]

theorem entropyClock_square_increment_ge_one (k : ℕ) :
    (entropyClock k)^2+1 ≤ (entropyClock (k+1))^2 := by
  have hp : 0 < (entropyClock (k+1))^2 := sq_pos_of_pos (lt_of_lt_of_le (by norm_num) (entropyClock_succ_ge_one k))
  have hb : 1 ≤ (entropyClock (k+1))^2 := by nlinarith [entropyClock_succ_ge_one k]
  have h := entropyClock_square_increment_identity k
  apply le_of_mul_le_mul_left (a := (entropyClock (k+1))^2) ?_ hp
  nlinarith only [h,hb]

theorem entropyClock_square_ge_rank (k : ℕ) : (k : ℝ) ≤ (entropyClock k)^2 := by
  induction k with
  | zero => norm_num [entropyClock]
  | succ k ih =>
    push_cast
    linarith [entropyClock_square_increment_ge_one k]

theorem entropyClock_square_increment_ge_198 {k : ℕ} (hk : 49 ≤ k) :
    (entropyClock k)^2+99/50 ≤ (entropyClock (k+1))^2 := by
  have hr : (50 : ℝ) ≤ (k+1 : ℕ) := by exact_mod_cast (show 50 ≤ k+1 by omega)
  have hb := hr.trans (entropyClock_square_ge_rank (k+1))
  have hp : 0 < (entropyClock (k+1))^2 := by linarith
  have h := entropyClock_square_increment_identity k
  apply le_of_mul_le_mul_left (a := (entropyClock (k+1))^2) ?_ hp
  nlinarith only [h,hb]

theorem entropyClock_square_ge_198_after_burnin (k : ℕ) :
    (99/50 : ℝ)*(k : ℝ) ≤ (entropyClock (50+k))^2 := by
  induction k with
  | zero => simpa using sq_nonneg (entropyClock 50)
  | succ k ih =>
    have h := entropyClock_square_increment_ge_198 (k:=50+k) (by omega)
    have heq : 50+(k+1)=(50+k)+1 := by omega
    rw [heq]
    push_cast
    nlinarith only [h,ih]

theorem entropyClock_pos {k : ℕ} (hk : 1 ≤ k) : 0 < entropyClock k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  exact lt_of_lt_of_le (by norm_num) (entropyClock_succ_ge_one j)

theorem entropyClock_le_succ (k : ℕ) : entropyClock k ≤ entropyClock (k+1) := by
  have h := entropyClock_square_increment_ge_one k
  nlinarith [entropyClock_nonneg k, entropyClock_nonneg (k+1)]

theorem entropyClock_monotone : Monotone entropyClock := by
  exact monotone_nat_of_le_succ entropyClock_le_succ

theorem entropyClock_after_burnin_ge (k : ℕ) :
    Real.sqrt (99/50 : ℝ)*Real.sqrt (k : ℝ) ≤ entropyClock (50+k) := by
  have h := Real.sqrt_le_sqrt (entropyClock_square_ge_198_after_burnin k)
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 99/50),
    Real.sqrt_sq (entropyClock_nonneg (50+k))] at h
  exact h

theorem entropyClock_inverse_after_burnin_le (k : ℕ) :
    1/entropyClock (51+k) ≤
      (1/Real.sqrt (99/50 : ℝ))*(1/Real.sqrt ((k : ℝ)+1)) := by
  have h := entropyClock_after_burnin_ge (k+1)
  rw [show 50+(k+1)=51+k by omega, Nat.cast_add, Nat.cast_one] at h
  have hp : 0 < Real.sqrt (99/50 : ℝ)*Real.sqrt ((k : ℝ)+1) := by positivity
  have hi := one_div_le_one_div_of_le hp h
  simpa only [one_div_mul_one_div] using hi

theorem entropy_reciprocal_sqrt_step_le {x : ℝ} (hx : 0 ≤ x) :
    1/Real.sqrt (x+1) ≤ 2*(Real.sqrt (x+1)-Real.sqrt x) := by
  have hs : 0 < Real.sqrt (x+1) := Real.sqrt_pos.mpr (by linarith)
  apply (div_le_iff₀ hs).mpr
  nlinarith [Real.sq_sqrt hx, Real.sq_sqrt (show 0 ≤ x+1 by linarith),
    sq_nonneg (Real.sqrt (x+1)-Real.sqrt x)]

theorem entropy_reciprocal_sqrt_sum_le (m : ℕ) :
    (∑ j ∈ Finset.range m, 1/Real.sqrt ((j : ℝ)+1)) ≤ 2*Real.sqrt (m : ℝ) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    have hs := entropy_reciprocal_sqrt_step_le (show 0 ≤ (m : ℝ) by positivity)
    rw [Finset.sum_range_succ]
    push_cast
    linarith only [ih,hs]

/-- After the fixed fifty-step prefix, the inverse clock has the sharp
square-root summability coefficient corresponding to growth at least1.98. -/
theorem entropyClock_inverse_tail_sum_le (m : ℕ) :
    (∑ j ∈ Finset.range m, 1/entropyClock (51+j)) ≤
      2*Real.sqrt (m : ℝ)/Real.sqrt (99/50 : ℝ) := by
  calc
    _ ≤ ∑ j ∈ Finset.range m,
        (1/Real.sqrt (99/50 : ℝ))*(1/Real.sqrt ((j : ℝ)+1)) := by
      apply Finset.sum_le_sum
      intro j _
      exact entropyClock_inverse_after_burnin_le j
    _ = (1/Real.sqrt (99/50 : ℝ)) *
        (∑ j ∈ Finset.range m, 1/Real.sqrt ((j : ℝ)+1)) := by rw [Finset.mul_sum]
    _ ≤ (1/Real.sqrt (99/50 : ℝ))*(2*Real.sqrt (m : ℝ)) := by
      exact mul_le_mul_of_nonneg_left (entropy_reciprocal_sqrt_sum_le m) (by positivity)
    _ = _ := by ring

theorem entropyClock_weighted_tail_sum_le {A : ℝ} (hA : 0 ≤ A) (m : ℕ) :
    (∑ j ∈ Finset.range m, A/entropyClock (51+j)) ≤
      2*A*Real.sqrt (m : ℝ)/Real.sqrt (99/50 : ℝ) := by
  have h := mul_le_mul_of_nonneg_left (entropyClock_inverse_tail_sum_le m) hA
  rw [Finset.mul_sum] at h
  simpa only [mul_one_div] using h.trans_eq (by ring)

theorem entropyClock_scaled_succ_equation {s : ℝ} (hs : 0 ≤ s) (k : ℕ) :
    (Real.sqrt s*entropyClock (k+1))^2 -
      (Real.sqrt s*entropyClock k)*(Real.sqrt s*entropyClock (k+1)) = s := by
  calc
    _ = (Real.sqrt s)^2*((entropyClock (k+1))^2-
        entropyClock k*entropyClock (k+1)) := by ring
    _ = s := by rw [entropyClock_succ_equation, Real.sq_sqrt hs, mul_one]

theorem entropyClock_displacement_tail_sum_le {t H s : ℝ}
    (ht : 0 ≤ t) (hH : 0 ≤ H) (hs : 0 < s) (m : ℕ) :
    (∑ j ∈ Finset.range m, t*(H/(Real.sqrt s*entropyClock (51+j)))) ≤
      2*(t*H/Real.sqrt s)*Real.sqrt (m : ℝ)/Real.sqrt (99/50 : ℝ) := by
  have h := entropyClock_weighted_tail_sum_le
    (show 0 ≤ t*H/Real.sqrt s by positivity) m
  convert h using 1
  apply Finset.sum_congr rfl
  intro j _
  ring

end KLS.ConstantReduction
end

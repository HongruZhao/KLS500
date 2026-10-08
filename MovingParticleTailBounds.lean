import SpectralReductionMovingJumpSumRecurrence
import SpectralReductionTripleGrowth

open scoped BigOperators
noncomputable section
namespace KLS.ConstantReduction

/-- A quadratic cap on each interval weight gives a cubic window bound. -/
theorem completeGeometricWindow_le_quadratic_cap {M : ℝ} (hM : 1 ≤ M) (q : ℕ) :
    completeGeometricWindow M q ≤
      (q : ℝ) * (((q : ℝ)+1)^2/4) * M^q := by
  have hM0 : 0 ≤ M := le_trans (by norm_num) hM
  unfold completeGeometricWindow
  calc
    _ ≤ ∑ _i : Fin q, (((q : ℝ)+1)^2/4)*M^q := by
      apply Finset.sum_le_sum
      intro i _
      have hc : completeIntervalWeight q i ≤ ((q : ℝ)+1)^2/4 := by
        unfold completeIntervalWeight
        nlinarith [sq_nonneg ((q : ℝ)+1-2*((i : ℕ)+1))]
      have hp : M^(i.rev : ℕ) ≤ M^q :=
        pow_le_pow_right₀ hM (Nat.le_of_lt i.rev.isLt)
      exact mul_le_mul hc hp (pow_nonneg hM0 _) (by positivity)
    _ = _ := by simp; ring

theorem completeGeometricWindow_triple_le_cubic {M : ℝ} (hM : 1 ≤ M)
    {d : ℕ} (hd : 1 ≤ d) :
    completeGeometricWindow M (3*d-1) ≤
      (27/4 : ℝ)*(d : ℝ)^3*(M^3)^d := by
  have hq : ((3*d-1 : ℕ) : ℝ) ≤ 3*(d : ℝ) := by
    exact_mod_cast Nat.sub_le (3*d) 1
  have hq1 : ((3*d-1 : ℕ) : ℝ)+1 = 3*(d : ℝ) := by
    exact_mod_cast (show 3*d-1+1=3*d by omega)
  have hp : M^(3*d-1) ≤ (M^3)^d := by
    rw [←pow_mul]
    exact pow_le_pow_right₀ hM (Nat.sub_le _ _)
  calc
    _ ≤ ((3*d-1 : ℕ) : ℝ)*((((3*d-1 : ℕ) : ℝ)+1)^2/4)*M^(3*d-1) :=
      completeGeometricWindow_le_quadratic_cap hM _
    _ = ((3*d-1 : ℕ) : ℝ)*((9/4 : ℝ)*(d : ℝ)^2)*M^(3*d-1) := by rw [hq1]; ring
    _ ≤ (3*(d : ℝ))*((9/4 : ℝ)*(d : ℝ)^2)*(M^3)^d := by
      gcongr
    _ = _ := by ring

theorem movingTripleRecoverySquared {d : ℕ} (hd : 1 ≤ d) :
    jumpRecoverySquared d d (3*d-1+1) = ((3*d).choose d : ℝ) := by
  unfold jumpRecoverySquared
  rw [show 3*d-1+1=3*d by omega, show 3*d-d=2*d by omega,
    show d+d=2*d by omega]
  have hh : ((2*d).choose d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.centralBinom_pos d).ne'
  field_simp

/-- The coefficient-one moving-particle recurrence has cubic tail growth. -/
theorem movingTripleErrorCoefficient_le_cubic {M : ℝ} (hM : 1 ≤ M)
    {d : ℕ} (hd : 1 ≤ d) :
    ((3*d-1 : ℕ) : ℝ) + movingJumpTaylorErrorCoefficient 1 d d (3*d-1) *
      completeGeometricWindow M (3*d-1) ≤
        (33/2 : ℝ)*(d : ℝ)^3*((27/4)*M^3)^d := by
  have hM0 : 0 ≤ M := le_trans (by norm_num) hM
  have hq : ((3*d-1 : ℕ) : ℝ) ≤ 3*(d : ℝ) := by
    exact_mod_cast Nat.sub_le (3*d) 1
  have hgam := triple_choose_le_power d
  have he : movingJumpTaylorErrorCoefficient 1 d d (3*d-1) ≤
      2*(27/4 : ℝ)^d := by
    unfold movingJumpTaylorErrorCoefficient
    rw [movingTripleRecoverySquared hd]
    norm_num only [div_one]
    linarith
  have hw0 : 0 ≤ completeGeometricWindow M (3*d-1) := by
    unfold completeGeometricWindow
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (completeIntervalWeight_nonneg i) (pow_nonneg hM0 _)
  have hh := add_le_add hq (mul_le_mul he
    (completeGeometricWindow_triple_le_cubic hM hd) hw0 (by positivity))
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdCube : (d : ℝ) ≤ (d : ℝ)^3 := by
    have hx := mul_nonneg (mul_nonneg (sub_nonneg.mpr hdR)
      (show (0 : ℝ) ≤ d by positivity)) (show (0 : ℝ) ≤ (d : ℝ)+1 by positivity)
    nlinarith
  have hb : (1 : ℝ) ≤ (27/4)*M^3 := by
    have hm : (1 : ℝ) ≤ M^3 := one_le_pow₀ hM
    nlinarith
  have hbd : (1 : ℝ) ≤ ((27/4)*M^3)^d := one_le_pow₀ hb
  have hsmall : 3*(d : ℝ) ≤ 3*(d : ℝ)^3*((27/4)*M^3)^d := by
    calc
      _ ≤ 3*(d : ℝ)^3 := by linarith
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hbd
  have hid : 2*(27/4 : ℝ)^d*((27/4 : ℝ)*(d : ℝ)^3*(M^3)^d) =
      (27/2 : ℝ)*(d : ℝ)^3*((27/4)*M^3)^d := by
    rw [mul_pow]
    ring
  rw [hid] at hh
  nlinarith

end KLS.ConstantReduction
end

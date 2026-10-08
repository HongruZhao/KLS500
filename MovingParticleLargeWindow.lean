import MovingParticleTailBounds
import Mathlib.Data.Nat.Factorial.BigOperators

open scoped BigOperators
noncomputable section
namespace KLS.ConstantReduction

/-- Comparison of the two descending factorial products in the recovery ratio. -/
theorem largeWindow_choose_ratio_bound {L d : ℕ} (hL : 3 ≤ L) :
    ((L*d).choose d : ℝ) ≤
      (((L : ℝ)-1)/((L : ℝ)-2))^d * (((L-1)*d).choose d : ℝ) := by
  let R : ℝ := ((L : ℝ)-1)/((L : ℝ)-2)
  have hLR : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have hden : (0 : ℝ) < (L : ℝ)-2 := by linarith
  have hR : 0 ≤ R := by
    dsimp [R]
    exact div_nonneg (by linarith) hden.le
  have hdL : d ≤ (L-1)*d := by
    simpa using Nat.mul_le_mul_right d (show 1 ≤ L-1 by omega)
  have hdL' : d ≤ L*d := by
    simpa using Nat.mul_le_mul_right d (show 1 ≤ L by omega)
  have hprod : ((L*d).descFactorial d : ℝ) ≤
      R^d * (((L-1)*d).descFactorial d : ℝ) := by
    rw [Nat.descFactorial_eq_prod_range,Nat.descFactorial_eq_prod_range]
    simp only [Nat.cast_prod]
    calc
      _ ≤ ∏ i ∈ Finset.range d, R*((((L-1)*d-i : ℕ) : ℝ)) := by
        apply Finset.prod_le_prod₀
        · intro i hi
          positivity
        · intro i hi
          have hid : i ≤ d := (Finset.mem_range.mp hi).le
          have hiL : i ≤ (L-1)*d := hid.trans hdL
          have hiL' : i ≤ L*d := hid.trans hdL'
          rw [Nat.cast_sub hiL',Nat.cast_sub hiL,Nat.cast_mul,Nat.cast_mul,
            Nat.cast_sub (by omega : 1 ≤ L)]
          dsimp [R]
          norm_num only [Nat.cast_one]
          rw [div_mul_eq_mul_div]
          apply (le_div_iff₀ hden).mpr
          have hh : (i : ℝ) ≤ d := by exact_mod_cast hid
          nlinarith
      _ = _ := by simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_range]
  rw [Nat.descFactorial_eq_factorial_mul_choose,Nat.descFactorial_eq_factorial_mul_choose,
    Nat.cast_mul,Nat.cast_mul] at hprod
  apply le_of_mul_le_mul_left (a:=(d.factorial : ℝ)) ?_ (by positivity)
  simpa only [mul_assoc,mul_left_comm,mul_comm] using hprod

/-- The recovery factor for a longer window has an explicit smaller exponential base. -/
theorem largeWindowRecoverySquared_le_power {L d : ℕ} (hL : 3 ≤ L) :
    jumpRecoverySquared d d (L*d) ≤
      (4*((L : ℝ)-1)/((L : ℝ)-2))^d := by
  have hLR : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have hdenR : (0 : ℝ) < (L : ℝ)-2 := by linarith
  have hR : 0 ≤ ((L : ℝ)-1)/((L : ℝ)-2) :=
    div_nonneg (by linarith) hdenR.le
  have hdL : d ≤ (L-1)*d := by
    simpa using Nat.mul_le_mul_right d (show 1 ≤ L-1 by omega)
  have hden : (0 : ℝ) < (((L-1)*d).choose d : ℝ) := by
    exact_mod_cast Nat.choose_pos hdL
  have hc := largeWindow_choose_ratio_bound (d:=d) hL
  have hcentral : ((2*d).choose d : ℝ) ≤ (4 : ℝ)^d := by
    exact_mod_cast Nat.centralBinom_le_four_pow d
  unfold jumpRecoverySquared
  rw [show L*d-d=(L-1)*d by rw [Nat.sub_mul,one_mul],show d+d=2*d by omega]
  apply (div_le_iff₀ hden).mpr
  calc
    _ ≤ ((((L : ℝ)-1)/((L : ℝ)-2))^d * (((L-1)*d).choose d : ℝ))*(4 : ℝ)^d :=
      mul_le_mul hc hcentral (by positivity) (by positivity)
    _ = _ := by rw [show 4*((L : ℝ)-1)/((L : ℝ)-2)=4*(((L : ℝ)-1)/((L : ℝ)-2)) by ring,mul_pow]; ring

/-- The same interval cap gives a cubic bound at any integer window multiple. -/
theorem completeGeometricWindow_largeWindow_le_cubic {M : ℝ} (hM : 1 ≤ M)
    {L d : ℕ} (hL : 3 ≤ L) (hd : 1 ≤ d) :
    completeGeometricWindow M (L*d-1) ≤
      ((L : ℝ)^3/4)*(d : ℝ)^3*(M^L)^d := by
  have hpLd : 1 ≤ L*d := by nlinarith
  have hq : ((L*d-1 : ℕ) : ℝ) ≤ (L : ℝ)*(d : ℝ) := by
    exact_mod_cast Nat.sub_le (L*d) 1
  have hq1 : ((L*d-1 : ℕ) : ℝ)+1=(L : ℝ)*(d : ℝ) := by
    exact_mod_cast (show L*d-1+1=L*d by omega)
  have hp : M^(L*d-1) ≤ (M^L)^d := by
    rw [←pow_mul]
    exact pow_le_pow_right₀ hM (Nat.sub_le _ _)
  calc
    _ ≤ ((L*d-1 : ℕ) : ℝ)*((((L*d-1 : ℕ) : ℝ)+1)^2/4)*M^(L*d-1) :=
      completeGeometricWindow_le_quadratic_cap hM _
    _ = ((L*d-1 : ℕ) : ℝ)*(((L : ℝ)*(d : ℝ))^2/4)*M^(L*d-1) := by rw [hq1]
    _ ≤ ((L : ℝ)*(d : ℝ))*(((L : ℝ)*(d : ℝ))^2/4)*(M^L)^d := by gcongr
    _ = _ := by ring

/-- A retained defect budget changes only the window term, with an explicit cubic tail. -/
theorem retainedLargeWindowErrorCoefficient_le_cubic {M δ : ℝ} (hM : 1 ≤ M) (hδ : 0 ≤ δ)
    {L d : ℕ} (hL : 3 ≤ L) (hd : 1 ≤ d) :
    ((L*d-1 : ℕ) : ℝ) + δ*movingJumpTaylorErrorCoefficient 1 d d (L*d-1)*
      completeGeometricWindow M (L*d-1) ≤
        ((L : ℝ)+δ*(L : ℝ)^3/2)*(d : ℝ)^3*
          ((4*((L : ℝ)-1)/((L : ℝ)-2))*M^L)^d := by
  let B : ℝ := 4*((L : ℝ)-1)/((L : ℝ)-2)
  have hLR : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have hden : (0 : ℝ) < (L : ℝ)-2 := by linarith
  have hR1 : (1 : ℝ) ≤ ((L : ℝ)-1)/((L : ℝ)-2) :=
    (le_div_iff₀ hden).mpr (by linarith)
  have hB : (1 : ℝ) ≤ B := by dsimp [B]; rw [mul_div_assoc]; linarith
  have hM0 : 0 ≤ M := le_trans (by norm_num) hM
  have hpLd : 1 ≤ L*d := by nlinarith
  have he : movingJumpTaylorErrorCoefficient 1 d d (L*d-1) ≤ 2*B^d := by
    unfold movingJumpTaylorErrorCoefficient
    rw [show L*d-1+1=L*d by omega]
    norm_num only [div_one]
    have hg := largeWindowRecoverySquared_le_power (d:=d) hL
    change jumpRecoverySquared d d (L*d) ≤ B^d at hg
    linarith
  have hw0 : 0 ≤ completeGeometricWindow M (L*d-1) := by
    unfold completeGeometricWindow
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (completeIntervalWeight_nonneg i) (pow_nonneg hM0 _)
  have hq : ((L*d-1 : ℕ) : ℝ) ≤ (L : ℝ)*(d : ℝ) := by
    exact_mod_cast Nat.sub_le (L*d) 1
  have hh := add_le_add hq (mul_le_mul
    (mul_le_mul_of_nonneg_left he hδ)
    (completeGeometricWindow_largeWindow_le_cubic hM hL hd) hw0 (by positivity))
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdCube : (d : ℝ) ≤ (d : ℝ)^3 := by
    have hx := mul_nonneg (mul_nonneg (sub_nonneg.mpr hdR)
      (show (0 : ℝ) ≤ d by positivity)) (show (0 : ℝ) ≤ (d : ℝ)+1 by positivity)
    nlinarith
  have hbase : (1 : ℝ) ≤ B*M^L := one_le_mul_of_one_le_of_one_le hB (one_le_pow₀ hM)
  have hbd : (1 : ℝ) ≤ (B*M^L)^d := one_le_pow₀ hbase
  have hsmall : (L : ℝ)*(d : ℝ) ≤ (L : ℝ)*(d : ℝ)^3*(B*M^L)^d := by
    calc
      _ ≤ (L : ℝ)*(d : ℝ)^3 := mul_le_mul_of_nonneg_left hdCube (by positivity)
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hbd
  have hid : (δ*(2*B^d))*(((L : ℝ)^3/4)*(d : ℝ)^3*(M^L)^d) =
      (δ*(L : ℝ)^3/2)*(d : ℝ)^3*(B*M^L)^d := by rw [mul_pow]; ring
  rw [hid] at hh
  change _ ≤ ((L : ℝ)+δ*(L : ℝ)^3/2)*(d : ℝ)^3*(B*M^L)^d
  nlinarith

end KLS.ConstantReduction
end

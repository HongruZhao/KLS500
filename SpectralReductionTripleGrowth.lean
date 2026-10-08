import SpectralReductionLongLemma38
import SpectralReductionIndividualWindow
import Mathlib.Data.Nat.Choose.Sum

open scoped BigOperators
noncomputable section
namespace KLS.ConstantReduction

theorem triple_choose_le_power (d : ℕ) :
    ((3*d).choose d : ℝ) ≤ (27/4 : ℝ)^d := by
  have hs := Finset.single_le_sum
    (s := Finset.range (3*d+1))
    (f := fun k : ℕ => (1 : ℝ)^k*2^(3*d-k)*((3*d).choose k : ℝ))
    (fun k _ => by positivity) (show d∈Finset.range (3*d+1) by simp; omega)
  rw [← add_pow] at hs
  have h2 : (2 : ℝ)^(2*d) = (4 : ℝ)^d := by rw [pow_mul]; norm_num
  have h3 : (3 : ℝ)^(3*d) = (27 : ℝ)^d := by rw [pow_mul]; norm_num
  norm_num only [one_pow, one_mul, show 3*d-d=2*d by omega, show (1:ℝ)+2=3 by norm_num] at hs
  rw [h2, h3] at hs
  rw [div_pow]
  exact (le_div_iff₀ (by positivity : (0 : ℝ)<4^d)).mpr (by nlinarith [hs])

theorem individualGeometricWindow_le_polynomial {M : ℝ} (hM : 1≤M) (q : ℕ) :
    individualGeometricWindow M q ≤ (q : ℝ)^2*M^q := by
  have hM0 : 0≤M := le_trans (by norm_num) hM
  unfold individualGeometricWindow
  calc
    _ ≤ ∑ _i : Fin q, (q : ℝ)*M^q := by
      apply Finset.sum_le_sum
      intro i _
      have hi : ((i : ℕ)+1 : ℝ)≤q := by exact_mod_cast i.isLt
      have hp : M^(i.rev : ℕ)≤M^q := pow_le_pow_right₀ hM (Nat.le_of_lt i.rev.isLt)
      exact mul_le_mul hi hp (pow_nonneg hM0 _) (Nat.cast_nonneg _)
    _ = _ := by simp; ring

theorem meanSymmetrizationCoefficient_long_le (d : ℕ) :
    meanSymmetrizationCoefficient (3*d-1) ≤ 5*(d : ℝ)^2 := by
  have hq : ((3*d-1 : ℕ) : ℝ)≤3*(d : ℝ) := by exact_mod_cast Nat.sub_le (3*d) 1
  by_cases hd : d=0
  · subst d; norm_num [meanSymmetrizationCoefficient]
  · have hd0 : 1≤d := by omega
    have hq1 : ((3*d-1 : ℕ) : ℝ)+1=3*(d : ℝ) := by
      exact_mod_cast (show 3*d-1+1=3*d by omega)
    unfold meanSymmetrizationCoefficient
    rw [hq1]
    nlinarith

theorem individualGeometricWindow_long_le {M : ℝ} (hM : 1≤M) (d : ℕ) :
    individualGeometricWindow M (3*d-1) ≤ 9*(d : ℝ)^2*(M^3)^d := by
  have hq : ((3*d-1 : ℕ) : ℝ)≤3*(d : ℝ) := by exact_mod_cast Nat.sub_le (3*d) 1
  have hsq : ((3*d-1 : ℕ) : ℝ)^2≤9*(d : ℝ)^2 := by
    nlinarith [Nat.cast_nonneg (α:=ℝ) (3*d-1)]
  have hp : M^(3*d-1)≤(M^3)^d := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ hM (Nat.sub_le _ _)
  exact (individualGeometricWindow_le_polynomial hM _).trans
    (mul_le_mul hsq hp (by positivity) (by positivity))

end KLS.ConstantReduction
end

import Mathlib

/-! The actual centered Laplace noise used in suspension: its density,
probability normalization, absolute moments, mean, and second moment. -/

open MeasureTheory Set Real
open scoped ENNReal
noncomputable section
namespace KLS

/-- The literal bilateral exponential density. -/
def laplaceNoiseDensity (β x : ℝ) : ℝ := β / 2 * Real.exp (-(β * |x|))

def laplaceNoiseLaw (β : ℝ) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (laplaceNoiseDensity β x))

lemma laplaceNoiseDensity_nonneg {β : ℝ} (hβ : 0 ≤ β) (x : ℝ) :
    0 ≤ laplaceNoiseDensity β x := by
  unfold laplaceNoiseDensity
  positivity

lemma continuous_laplaceNoiseDensity (β : ℝ) : Continuous (laplaceNoiseDensity β) := by
  unfold laplaceNoiseDensity
  fun_prop

lemma integral_abs_pow_exp_neg_mul_abs {β : ℝ} (hβ : 0 < β) (k : ℕ) :
    (∫ x : ℝ, |x| ^ k * Real.exp (-(β * |x|))) =
      2 * ((1 / β) ^ (k + 1) * (k.factorial : ℝ)) := by
  rw [integral_comp_abs (f := fun x : ℝ => x ^ k * Real.exp (-(β * x)))]
  congr 1
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (k : ℝ) + 1)
    (by positivity) hβ
  have he : (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) := by simp
  simp only [add_sub_cancel_right, Real.rpow_natCast, Real.Gamma_nat_eq_factorial] at h
  rw [he, Real.rpow_natCast] at h
  exact h

lemma integral_abs_pow_laplaceNoiseDensity {β : ℝ} (hβ : 0 < β) (k : ℕ) :
    (∫ x : ℝ, |x| ^ k * laplaceNoiseDensity β x) =
      (k.factorial : ℝ) / β ^ k := by
  calc
    _ = β / 2 * ∫ x : ℝ, |x| ^ k * Real.exp (-(β * |x|)) := by
      rw [← integral_const_mul]
      congr 1
      funext x
      unfold laplaceNoiseDensity
      ring
    _ = β / 2 * (2 * ((1 / β) ^ (k + 1) * (k.factorial : ℝ))) := by
      rw [integral_abs_pow_exp_neg_mul_abs hβ]
    _ = _ := by
      rw [div_pow, one_pow, pow_succ]
      field_simp [hβ.ne']

lemma integrable_abs_pow_laplaceNoiseDensity {β : ℝ} (hβ : 0 < β) (k : ℕ) :
    Integrable (fun x : ℝ => |x| ^ k * laplaceNoiseDensity β x) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_abs_pow_laplaceNoiseDensity hβ]
  exact div_ne_zero (by exact_mod_cast Nat.factorial_ne_zero k) (pow_ne_zero _ hβ.ne')

lemma integral_laplaceNoiseDensity {β : ℝ} (hβ : 0 < β) :
    (∫ x : ℝ, laplaceNoiseDensity β x) = 1 := by
  simpa using integral_abs_pow_laplaceNoiseDensity hβ 0

lemma integrable_laplaceNoiseDensity {β : ℝ} (hβ : 0 < β) :
    Integrable (laplaceNoiseDensity β) := by
  simpa using integrable_abs_pow_laplaceNoiseDensity hβ 0

lemma isProbabilityMeasure_laplaceNoiseLaw {β : ℝ} (hβ : 0 < β) :
    IsProbabilityMeasure (laplaceNoiseLaw β) where
  measure_univ := by
    rw [laplaceNoiseLaw, withDensity_apply _ MeasurableSet.univ]
    rw [Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal
      (integrable_laplaceNoiseDensity hβ)
      (ae_of_all _ (laplaceNoiseDensity_nonneg hβ.le)), integral_laplaceNoiseDensity hβ]
    simp

lemma integrable_laplaceNoiseLaw_iff {β : ℝ} (hβ : 0 ≤ β) (g : ℝ → ℝ) :
    Integrable g (laplaceNoiseLaw β) ↔
      Integrable (fun x => laplaceNoiseDensity β x * g x) := by
  rw [laplaceNoiseLaw, integrable_withDensity_iff_integrable_smul'
    ((continuous_laplaceNoiseDensity β).measurable.ennreal_ofReal)
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (laplaceNoiseDensity_nonneg hβ _), smul_eq_mul]

lemma integral_laplaceNoiseLaw {β : ℝ} (hβ : 0 ≤ β) (g : ℝ → ℝ) :
    (∫ x, g x ∂laplaceNoiseLaw β) = ∫ x, laplaceNoiseDensity β x * g x := by
  rw [laplaceNoiseLaw, integral_withDensity_eq_integral_toReal_smul
    ((continuous_laplaceNoiseDensity β).measurable.ennreal_ofReal)
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (laplaceNoiseDensity_nonneg hβ _), smul_eq_mul]

lemma integrable_abs_pow_laplaceNoiseLaw {β : ℝ} (hβ : 0 < β) (k : ℕ) :
    Integrable (fun x : ℝ => |x| ^ k) (laplaceNoiseLaw β) := by
  rw [integrable_laplaceNoiseLaw_iff hβ.le]
  simpa only [mul_comm] using integrable_abs_pow_laplaceNoiseDensity hβ k

lemma integral_abs_pow_laplaceNoiseLaw {β : ℝ} (hβ : 0 < β) (k : ℕ) :
    (∫ x : ℝ, |x| ^ k ∂laplaceNoiseLaw β) = (k.factorial : ℝ) / β ^ k := by
  rw [integral_laplaceNoiseLaw hβ.le]
  simpa only [mul_comm] using integral_abs_pow_laplaceNoiseDensity hβ k

lemma integrable_id_laplaceNoiseLaw {β : ℝ} (hβ : 0 < β) :
    Integrable (fun x : ℝ => x) (laplaceNoiseLaw β) := by
  apply (integrable_norm_iff (by fun_prop)).1
  simpa only [pow_one, Real.norm_eq_abs] using integrable_abs_pow_laplaceNoiseLaw hβ 1

lemma integral_id_laplaceNoiseLaw {β : ℝ} (hβ : 0 < β) :
    (∫ x : ℝ, x ∂laplaceNoiseLaw β) = 0 := by
  rw [integral_laplaceNoiseLaw hβ.le]
  have h := integral_neg_eq_self (fun x : ℝ => laplaceNoiseDensity β x * x) volume
  have he : (fun x : ℝ => laplaceNoiseDensity β (-x) * (-x)) =
      fun x => -(laplaceNoiseDensity β x * x) := by
    funext x
    simp [laplaceNoiseDensity]
  rw [he, integral_neg] at h
  linarith

lemma integrable_sq_laplaceNoiseLaw {β : ℝ} (hβ : 0 < β) :
    Integrable (fun x : ℝ => x ^ 2) (laplaceNoiseLaw β) := by
  simpa only [sq_abs] using integrable_abs_pow_laplaceNoiseLaw hβ 2

lemma integral_sq_laplaceNoiseLaw {β : ℝ} (hβ : 0 < β) :
    (∫ x : ℝ, x ^ 2 ∂laplaceNoiseLaw β) = 2 / β ^ 2 := by
  simpa only [sq_abs, Nat.factorial_two, Nat.cast_ofNat] using
    integral_abs_pow_laplaceNoiseLaw hβ 2

/-- Exponential absolute moments are integrable on the actual open interval
below the noise rate. This supplies a genuine local exponential-moment domain. -/
lemma integrable_exp_mul_abs_laplaceNoiseLaw {β t : ℝ} (hβ : 0 < β) (ht : t < β) :
    Integrable (fun x : ℝ => Real.exp (t * |x|)) (laplaceNoiseLaw β) := by
  rw [integrable_laplaceNoiseLaw_iff hβ.le]
  have hδ : 0 < β - t := sub_pos.2 ht
  have he : (fun x : ℝ => laplaceNoiseDensity β x * Real.exp (t * |x|)) =
      fun x => (β / (β - t)) * laplaceNoiseDensity (β - t) x := by
    funext x
    calc
      _ = (β / 2) * Real.exp (-((β - t) * |x|)) := by
        unfold laplaceNoiseDensity
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ = _ := by
        unfold laplaceNoiseDensity
        field_simp [hδ.ne']
  rw [he]
  exact (integrable_laplaceNoiseDensity hδ).const_mul _

lemma integral_exp_mul_abs_laplaceNoiseLaw {β t : ℝ} (hβ : 0 < β) (ht : t < β) :
    (∫ x : ℝ, Real.exp (t * |x|) ∂laplaceNoiseLaw β) = β / (β - t) := by
  rw [integral_laplaceNoiseLaw hβ.le]
  have hδ : 0 < β - t := sub_pos.2 ht
  have he : (fun x : ℝ => laplaceNoiseDensity β x * Real.exp (t * |x|)) =
      fun x => (β / (β - t)) * laplaceNoiseDensity (β - t) x := by
    funext x
    calc
      _ = (β / 2) * Real.exp (-((β - t) * |x|)) := by
        unfold laplaceNoiseDensity
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ = _ := by
        unfold laplaceNoiseDensity
        field_simp [hδ.ne']
  rw [he, integral_const_mul, integral_laplaceNoiseDensity hδ, mul_one]

end KLS
end
#print axioms KLS.isProbabilityMeasure_laplaceNoiseLaw
#print axioms KLS.integral_id_laplaceNoiseLaw
#print axioms KLS.integral_sq_laplaceNoiseLaw

#print axioms KLS.integrable_exp_mul_abs_laplaceNoiseLaw
#print axioms KLS.integral_exp_mul_abs_laplaceNoiseLaw

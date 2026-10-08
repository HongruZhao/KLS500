import KLS.WeightedExponentialMoments

/-! Genuine polynomial-times-radial-exponential moments for the strongly
convex potential measure. These provide local domination for arbitrary L²
tilt observables, without a compact-support or polynomial-growth premise. -/

open MeasureTheory InnerProductSpace Set Filter Matrix
open scoped ContDiff RealInnerProductSpace

noncomputable section
namespace KLS
variable {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
  (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
  (hlower : ∀ y (v : Fin n → ℝ),
    κ * (v ⬝ᵥ v) ≤ v ⬝ᵥ (coordinateHessian φ y *ᵥ v))

include hφ hκ hlower

theorem integrable_exp_mul_norm_potentialMeasure (a : ℝ) :
    Integrable (fun x => Real.exp (a * ‖x‖)) (potentialMeasure φ) := by
  rw [integrable_potentialMeasure_iff hφ.continuous.measurable]
  let B : ℝ := |a| + ‖gradient φ 0‖ + 1
  let A : ℝ := B ^ 2 / (2 * κ) - φ 0
  have hb (x : Space n) : ‖x‖ - A ≤ φ x - a * ‖x‖ := by
    have hq := potential_quadratic_lower_bound hφ hlower x
    have hgn := abs_real_inner_le_norm (gradient φ 0) x
    have hg := neg_le_abs (inner ℝ (gradient φ 0) x)
    have ha := mul_le_mul_of_nonneg_right (le_abs_self a) (norm_nonneg x)
    have hs := sq_nonneg (κ * ‖x‖ - B)
    have hden : 0 < 2 * κ := by positivity
    have hdiv : (2 * κ) * (B ^ 2 / (2 * κ)) = B ^ 2 :=
      mul_div_cancel₀ _ (ne_of_gt hden)
    dsimp [A, B] at *
    nlinarith
  have hc : Continuous (fun x : Space n => φ x - a * ‖x‖) :=
    hφ.continuous.sub (continuous_const.mul continuous_norm)
  have hi := integrable_exp_neg_of_linear_coercivity hc.aestronglyMeasurable
    (by norm_num : (0 : ℝ) < 1) (by simpa only [one_mul] using hb)
  convert hi using 1
  funext x
  rw [← Real.exp_add]
  congr 1
  ring

theorem integrable_norm_pow_mul_exp_norm_potentialMeasure (m : ℕ) (a : ℝ) :
    Integrable (fun x => ‖x‖ ^ m * Real.exp (a * ‖x‖)) (potentialMeasure φ) := by
  apply ((integrable_exp_mul_norm_potentialMeasure hφ hκ hlower (a + 1)).const_mul
    (m.factorial : ℝ)).mono' (by fun_prop)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hm : (0 : ℝ) < m.factorial := by exact_mod_cast m.factorial_pos
  have hp := (div_le_iff₀ hm).mp (Real.pow_div_factorial_le_exp ‖x‖ (norm_nonneg x) m)
  have hh := mul_le_mul_of_nonneg_right hp (Real.exp_pos (a * ‖x‖)).le
  calc
    _ ≤ (Real.exp ‖x‖ * (m.factorial : ℝ)) * Real.exp (a * ‖x‖) := hh
    _ = _ := by
      rw [mul_comm (Real.exp ‖x‖) (m.factorial : ℝ), mul_assoc, ← Real.exp_add]
      congr 2
      ring

theorem memLp_norm_pow_mul_exp_norm_potentialMeasure (m : ℕ) (a : ℝ) :
    MemLp (fun x => ‖x‖ ^ m * Real.exp (a * ‖x‖)) 2 (potentialMeasure φ) := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  convert integrable_norm_pow_mul_exp_norm_potentialMeasure hφ hκ hlower (m * 2) (2 * a) using 1
  funext x
  rw [mul_pow, ← pow_mul, pow_two, ← Real.exp_add]
  congr 2
  ring

theorem integrable_abs_mul_norm_pow_exp_norm_of_memLp
    {f : Space n → ℝ} (hf : MemLp f 2 (potentialMeasure φ)) (m : ℕ) (a : ℝ) :
    Integrable (fun x => ‖f x‖ * ‖x‖ ^ m * Real.exp (a * ‖x‖)) (potentialMeasure φ) := by
  convert hf.norm.integrable_mul (memLp_norm_pow_mul_exp_norm_potentialMeasure hφ hκ hlower m a) using 1
  funext x
  change ‖f x‖ * ‖x‖ ^ m * Real.exp (a * ‖x‖) = ‖f x‖ * (‖x‖ ^ m * Real.exp (a * ‖x‖))
  ring

end KLS
end

#print axioms KLS.integrable_exp_mul_norm_potentialMeasure
#print axioms KLS.integrable_norm_pow_mul_exp_norm_potentialMeasure
#print axioms KLS.memLp_norm_pow_mul_exp_norm_potentialMeasure
#print axioms KLS.integrable_abs_mul_norm_pow_exp_norm_of_memLp

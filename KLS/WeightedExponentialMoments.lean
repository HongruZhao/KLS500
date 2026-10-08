import KLS.WeightedConfinement
import KLS.MomentExponentialTails

/-! The actual lower Hessian bound gives every linear exponential moment.
No upper derivative bound or polynomial growth assumption is used. -/

open MeasureTheory InnerProductSpace Set Filter Matrix
open scoped ContDiff RealInnerProductSpace

noncomputable section
namespace KLS
variable {n : ℕ}

/-- A lower Hessian bound supplies the genuine quadratic tangent bound. -/
theorem potential_quadratic_lower_bound {φ : Space n → ℝ} {κ : ℝ}
    (hφ : ContDiff ℝ 2 φ)
    (hlower : ∀ y (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ y *ᵥ a)) (x : Space n) :
    φ 0 + inner ℝ (gradient φ 0) x + κ / 2 * ‖x‖ ^ 2 ≤ φ x := by
  let a : ℝ := inner ℝ (gradient φ 0) x
  let F : ℝ → ℝ := fun t => φ (t • x) - t * a - κ / 2 * t ^ 2 * ‖x‖ ^ 2
  have hD (t : ℝ) : HasDerivAt F
      (fderiv ℝ φ (t • x) x - a - κ * t * ‖x‖ ^ 2) t := by
    have hp := (hφ.differentiable (by norm_num) (t • x)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).smul_const x)
    have hh := (hp.sub ((hasDerivAt_id t).mul_const a)).sub
      (((hasDerivAt_id t).pow 2).const_mul (κ / 2) |>.mul_const (‖x‖ ^ 2))
    convert hh using 1
    · rfl
    · simp only [one_smul, id_eq, show (2 - 1 : ℕ) = 1 from rfl, pow_one,
        Nat.cast_ofNat, mul_one, one_mul]
      ring
  have hlow (t : ℝ) (ht : t ∈ interior (Icc (0 : ℝ) 1)) : 0 ≤ deriv F t := by
    rw [interior_Icc] at ht
    have hb := radial_gradient_lower_bound_of_hessian hφ hlower (t • x)
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inner_smul_right,
      conj_trivial] at hb
    rw [inner_gradient_left, inner_gradient_left] at hb
    rw [(hD t).deriv]
    have hp : 0 ≤ t * (fderiv ℝ φ (t • x) x - a - κ * t * ‖x‖ ^ 2) := by
      dsimp [a]
      rw [inner_gradient_left]
      nlinarith
    exact nonneg_of_mul_nonneg_right hp ht.1
  have hh := (convex_Icc (0 : ℝ) 1).mul_sub_le_image_sub_of_le_deriv
    (fun t _ => (hD t).continuousAt.continuousWithinAt)
    (fun t _ => (hD t).differentiableAt.differentiableWithinAt) hlow
    0 (by simp) 1 (by simp) (by norm_num)
  simp only [F, zero_smul, one_smul, zero_mul, one_mul, zero_pow, one_pow,
    sub_zero] at hh
  dsimp [a] at hh
  linarith

/-- Every linear exponential is integrable for the actual strongly convex density. -/
theorem integrable_exp_inner_potentialMeasure {φ : Space n → ℝ} {κ : ℝ}
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ y (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ y *ᵥ a)) (z : Space n) :
    Integrable (fun x => Real.exp (inner ℝ z x)) (potentialMeasure φ) := by
  rw [integrable_potentialMeasure_iff hφ.continuous.measurable]
  let B : ℝ := ‖z‖ + ‖gradient φ 0‖ + 1
  let A : ℝ := B ^ 2 / (2 * κ) - φ 0
  have hb (x : Space n) :
      ‖x‖ - A ≤ φ x - inner ℝ z x := by
    have hq := potential_quadratic_lower_bound hφ hlower x
    have hz := real_inner_le_norm z x
    have hg := neg_le_abs (inner ℝ (gradient φ 0) x)
    have hgn := abs_real_inner_le_norm (gradient φ 0) x
    have hs := sq_nonneg (κ * ‖x‖ - B)
    have hden : 0 < 2 * κ := by positivity
    have hdiv : (2 * κ) * (B ^ 2 / (2 * κ)) = B ^ 2 :=
      mul_div_cancel₀ _ (ne_of_gt hden)
    dsimp [A, B] at *
    nlinarith
  have hcont : Continuous (fun x : Space n => φ x - inner ℝ z x) :=
    hφ.continuous.sub (by fun_prop)
  have hi := integrable_exp_neg_of_linear_coercivity (φ := fun x => φ x - inner ℝ z x)
    hcont.aestronglyMeasurable (by norm_num : (0 : ℝ) < 1)
    (by simpa only [one_mul] using hb)
  convert hi using 1
  funext x
  rw [← Real.exp_add]
  congr 1
  ring

/-- The exponential weight needed for the L² tilt pairing is genuinely in L². -/
theorem memLp_exp_inner_potentialMeasure {φ : Space n → ℝ} {κ : ℝ}
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ y (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ y *ᵥ a)) (z : Space n) :
    MemLp (fun x => Real.exp (inner ℝ z x)) 2 (potentialMeasure φ) := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  convert integrable_exp_inner_potentialMeasure hφ hκ hlower ((2 : ℝ) • z) using 1
  funext x
  rw [inner_smul_left]
  simp only [conj_trivial]
  rw [← Real.exp_nat_mul]
  norm_num

end KLS
end

#print axioms KLS.potential_quadratic_lower_bound
#print axioms KLS.integrable_exp_inner_potentialMeasure
#print axioms KLS.memLp_exp_inner_potentialMeasure

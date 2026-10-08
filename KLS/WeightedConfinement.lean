import KLS.WeightedEnergyCoercivity
import KLS.SmoothCutoffSequence
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Actual confinement from a lower Hessian bound

The radial drift estimate is obtained by differentiating the actual gradient
along a line. Compact integration by parts then controls a weighted second
moment by the actual value and derivative energies. No upper Hessian bound
or class-uniform Poincaré constant is assumed.
-/

open MeasureTheory ProbabilityTheory InnerProductSpace Set Filter Matrix
open scoped ContDiff RealInnerProductSpace

noncomputable section
namespace KLS
variable {n : ℕ}

lemma euclidean_coordinate_dot_self (x : Space n) :
    (fun i : Fin n => x i) ⬝ᵥ (fun i : Fin n => x i) = ‖x‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro i _
  simp [Real.norm_eq_abs, pow_two]

/-- The actual Hessian lower bound gives a lower bound on radial growth of the actual gradient. -/
theorem radial_gradient_lower_bound_of_hessian {φ : Space n → ℝ} {κ : ℝ}
    (hφ : ContDiff ℝ 2 φ)
    (hlower : ∀ y (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ y *ᵥ a)) (x : Space n) :
    κ * ‖x‖ ^ 2 ≤ inner ℝ (gradient φ x) x - inner ℝ (gradient φ 0) x := by
  have hddφ : Differentiable ℝ (fderiv ℝ φ) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  let F : ℝ → ℝ := fun t => fderiv ℝ φ (t • x) x
  have hD (t : ℝ) : HasDerivAt F (fderiv ℝ (fderiv ℝ φ) (t • x) x x) t := by
    have hmap := (hddφ (t • x)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).smul_const x)
    simpa [F] using hmap.clm_apply (hasDerivAt_const t x)
  have hDlower (t : ℝ) : κ * ‖x‖ ^ 2 ≤ deriv F t := by
    rw [(hD t).deriv, ← coordinateHessian_quadratic_eq hφ (t • x) x x,
      matrix_quadratic_sum_eq_dotProduct]
    simpa only [euclidean_coordinate_dot_self] using hlower (t • x) (fun i => x i)
  have h := mul_sub_le_image_sub_of_le_deriv (fun t => (hD t).differentiableAt)
    hDlower (by norm_num : (0 : ℝ) ≤ 1)
  simpa only [F, sub_zero, mul_one, one_smul, zero_smul, inner_gradient_left] using h

/-- A pointwise confinement estimate with the actual drift at the origin. -/
theorem radial_gradient_lower_bound_norm {φ : Space n → ℝ} {κ : ℝ}
    (hφ : ContDiff ℝ 2 φ)
    (hlower : ∀ y (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ y *ᵥ a)) (x : Space n) :
    κ * ‖x‖ ^ 2 ≤ inner ℝ (gradient φ x) x + ‖gradient φ 0‖ * ‖x‖ := by
  have h := radial_gradient_lower_bound_of_hessian hφ hlower x
  have hc := neg_le_abs (inner ℝ (gradient φ 0) x)
  have hi := abs_real_inner_le_norm (gradient φ 0) x
  linarith


lemma gradient_half_norm_sq (x : Space n) : gradient (fun y : Space n => ‖y‖ ^ 2 / 2) x = x := by
  apply (toDual ℝ (Space n)).injective
  rw [toDual_gradient]
  have hd := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.mul_const (2 : ℝ)⁻¹
  simp only [← div_eq_mul_inv] at hd
  rw [hd.fderiv]
  ext y
  simp only [_root_.smul_apply, smul_eq_mul, innerSL_apply_apply, toDual_apply_apply]
  ring

lemma coordinateHessian_half_norm_sq (x : Space n) :
    coordinateHessian (fun y : Space n => ‖y‖ ^ 2 / 2) x = (1 : Matrix (Fin n) (Fin n) ℝ) := by
  ext i j
  have heq : coordinateDerivative (fun y : Space n => ‖y‖ ^ 2 / 2) j = fun y : Space n => y j := by
    funext y
    rw [coordinateDerivative_eq_gradient, gradient_half_norm_sq]
  change coordinateDerivative (coordinateDerivative (fun y : Space n => ‖y‖ ^ 2 / 2) j) i x = _
  rw [heq]
  change (fderiv ℝ (EuclideanSpace.proj (𝕜 := ℝ) j) x) (EuclideanSpace.single i 1) = _
  rw [ContinuousLinearMap.fderiv]
  simp [Matrix.one_apply, eq_comm]

/-- Compact support justifies the exact actual weighted radial integration identity. -/
theorem weighted_radial_identity_compact {φ f : Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    (∫ x, inner ℝ (gradient φ x) x * f x ^ 2 ∂potentialMeasure φ) =
      (n : ℝ) * (∫ x, f x ^ 2 ∂potentialMeasure φ) +
        2 * ∫ x, f x * inner ℝ (gradient f x) x ∂potentialMeasure φ := by
  have hq : ContDiff ℝ 2 (fun x : Space n => ‖x‖ ^ 2 / 2) :=
    (contDiff_norm_sq ℝ).div_const 2
  have hqdiff (x : Space n) : weightedDiffusion φ (fun y : Space n => ‖y‖ ^ 2 / 2) x =
      (n : ℝ) - inner ℝ (gradient φ x) x := by
    simp [weightedDiffusion, coordinateLaplacian, coordinateHessian_half_norm_sq, gradient_half_norm_sq]
  have hf2c : HasCompactSupport (fun x => f x ^ 2) := by
    have ht := (hc.mul_right : HasCompactSupport (f * f))
    change HasCompactSupport (fun x => f x * f x) at ht
    simpa only [pow_two] using ht
  have hJ : Integrable (fun x => f x ^ 2) (potentialMeasure φ) :=
    integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      (hf.continuous.pow 2) hf2c
  have hD : Integrable (fun x => inner ℝ (gradient φ x) x * f x ^ 2) (potentialMeasure φ) :=
    integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      (((continuous_gradient_of_contDiff hφ).inner continuous_id).mul (hf.continuous.pow 2)) hf2c.mul_left
  have hC : Integrable (fun x => f x * inner ℝ (gradient f x) x) (potentialMeasure φ) :=
    integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      (hf.continuous.mul ((continuous_gradient_of_contDiff hf).inner continuous_id)) hc.mul_right
  have hibp := integral_mul_weightedDiffusion_of_hasCompactSupport_left hφ (hf.mul hf) hq (hc.mul_right : HasCompactSupport (f * f))
  have hl : (∫ x, (f x * f x) * weightedDiffusion φ (fun y : Space n => ‖y‖ ^ 2 / 2) x
      ∂potentialMeasure φ) = (n : ℝ) * (∫ x, f x ^ 2 ∂potentialMeasure φ) -
        ∫ x, inner ℝ (gradient φ x) x * f x ^ 2 ∂potentialMeasure φ := by
    rw [← integral_const_mul, ← integral_sub (hJ.const_mul (n : ℝ)) hD]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by dsimp only; rw [hqdiff]; ring
  have hr : (∫ x, inner ℝ (gradient (fun y => f y * f y) x)
      (gradient (fun y : Space n => ‖y‖ ^ 2 / 2) x) ∂potentialMeasure φ) =
      2 * ∫ x, f x * inner ℝ (gradient f x) x ∂potentialMeasure φ := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only
      rw [gradient_half_norm_sq, gradient_mul_real (hf.differentiable (by norm_num) x)
        (hf.differentiable (by norm_num) x)]
      simp only [inner_add_left, inner_smul_left, conj_trivial]
      ring
  rw [hl, hr] at hibp
  linarith

/-- The actual lower Hessian and compact weighted integration by parts yield confinement. -/
theorem weighted_confinement_compact {φ f : Space n → ℝ} {κ : ℝ}
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ y (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ y *ᵥ a))
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    κ ^ 2 * (∫ x, ‖x‖ ^ 2 * f x ^ 2 ∂potentialMeasure φ) ≤
      (2 * κ * n + 2 * ‖gradient φ 0‖ ^ 2) * (∫ x, f x ^ 2 ∂potentialMeasure φ) +
        8 * ∫ x, ‖gradient f x‖ ^ 2 ∂potentialMeasure φ := by
  have hf2c : HasCompactSupport (fun x => f x ^ 2) := by
    have ht := (hc.mul_right : HasCompactSupport (f * f))
    change HasCompactSupport (fun x => f x * f x) at ht
    simpa only [pow_two] using ht
  have hJ : Integrable (fun x => f x ^ 2) (potentialMeasure φ) :=
    integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      (hf.continuous.pow 2) hf2c
  have hQ : Integrable (fun x => ‖x‖ ^ 2 * f x ^ 2) (potentialMeasure φ) :=
    integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      ((continuous_norm.pow 2).mul (hf.continuous.pow 2)) hf2c.mul_left
  have hD : Integrable (fun x => inner ℝ (gradient φ x) x * f x ^ 2) (potentialMeasure φ) :=
    integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      (((continuous_gradient_of_contDiff (hφ.of_le (by norm_num))).inner continuous_id).mul
        (hf.continuous.pow 2)) hf2c.mul_left
  have hC : Integrable (fun x => f x * inner ℝ (gradient f x) x) (potentialMeasure φ) :=
    integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      (hf.continuous.mul ((continuous_gradient_of_contDiff hf).inner continuous_id)) hc.mul_right
  have hE : Integrable (fun x => ‖gradient f x‖ ^ 2) (potentialMeasure φ) :=
    integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      ((continuous_gradient_of_contDiff hf).norm.pow 2)
      (by
        have ht := ((hasCompactSupport_gradient hc).norm.mul_right :
          HasCompactSupport ((fun x => ‖gradient f x‖) * (fun x => ‖gradient f x‖)))
        change HasCompactSupport (fun x => ‖gradient f x‖ * ‖gradient f x‖) at ht
        simpa only [pow_two] using ht)
  have hpoint (x : Space n) :
      κ ^ 2 * (‖x‖ ^ 2 * f x ^ 2) ≤
        ((2 * κ) * (inner ℝ (gradient φ x) x * f x ^ 2) -
          (4 * κ) * (f x * inner ℝ (gradient f x) x)) +
          (2 * ‖gradient φ 0‖ ^ 2) * f x ^ 2 + 8 * ‖gradient f x‖ ^ 2 := by
    have hr := mul_le_mul_of_nonneg_right (radial_gradient_lower_bound_norm hφ hlower x)
      (mul_nonneg hκ.le (sq_nonneg (f x)))
    have hs₁ := sq_nonneg (κ * ‖x‖ * f x / 2 - ‖gradient φ 0‖ * f x)
    have hs₂ := real_inner_self_nonneg (x := (κ * f x / 2) • x - (2 : ℝ) • gradient f x)
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      conj_trivial, real_inner_self_eq_norm_sq] at hs₂
    rw [real_inner_comm (gradient f x) x] at hs₂
    nlinarith
  have hi := integral_mono (hQ.const_mul (κ ^ 2))
    ((((hD.const_mul (2 * κ)).sub (hC.const_mul (4 * κ))).add
      (hJ.const_mul (2 * ‖gradient φ 0‖ ^ 2))).add (hE.const_mul 8)) hpoint
  have hrhs := integral_add
    (((hD.const_mul (2 * κ)).sub (hC.const_mul (4 * κ))).add
      (hJ.const_mul (2 * ‖gradient φ 0‖ ^ 2))) (hE.const_mul 8)
  have hrhs' := integral_add ((hD.const_mul (2 * κ)).sub (hC.const_mul (4 * κ)))
      (hJ.const_mul (2 * ‖gradient φ 0‖ ^ 2))
  have hrhs'' := integral_sub (hD.const_mul (2 * κ)) (hC.const_mul (4 * κ))
  simp only [Pi.add_apply, Pi.sub_apply] at hrhs hrhs' hrhs'' hi
  rw [integral_const_mul, hrhs, hrhs', hrhs'', integral_const_mul,
    integral_const_mul, integral_const_mul, integral_const_mul] at hi
  have hid := weighted_radial_identity_compact (hφ.of_le (by norm_num)) hf hc
  nlinarith

end KLS
end

#print axioms KLS.radial_gradient_lower_bound_of_hessian
#print axioms KLS.radial_gradient_lower_bound_norm

#print axioms KLS.weighted_radial_identity_compact
#print axioms KLS.weighted_confinement_compact

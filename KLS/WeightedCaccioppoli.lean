import KLS.WeightedCompactSupport

/-!
# Classical weighted Caccioppoli estimate from actual integration by parts

The first integration factor may be compact while the differentiated function
is not. A genuine C² solution of `Lφ h = 0` then satisfies the cutoff energy
estimate with constant 4. No weak-to-classical regularity is asserted.
-/

open MeasureTheory InnerProductSpace Filter
open scoped ContDiff

noncomputable section
namespace KLS

variable {n : ℕ}

/-- Compactness of the undifferentiated integration factor also suffices for the actual domain. -/
theorem diffusionIntegrability_of_hasCompactSupport_left {φ f g : Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 2 g)
    (hc : HasCompactSupport f) : DiffusionIntegrability φ f g := by
  have hdcφ (i : Fin n) : Continuous (coordinateDerivative φ i) :=
    (contDiff_coordinateDerivative hφ (m := 0) (by norm_num) i).continuous
  have hdcf (i : Fin n) : Continuous (coordinateDerivative f i) :=
    (contDiff_coordinateDerivative hf (m := 0) (by norm_num) i).continuous
  have hdcg (i : Fin n) : Continuous (coordinateDerivative g i) :=
    (contDiff_coordinateDerivative hg (m := 0) (by norm_num) i).continuous
  have hddcg (i : Fin n) : Continuous (fun x => coordinateHessian g x i i) :=
    (contDiff_coordinateHessian hg (m := 0) (by norm_num) i i).continuous
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    exact integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      (hf.continuous.mul (hdcg i)) hc.mul_right
  · intro i
    exact integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      ((hdcf i).mul (hdcg i)) (hasCompactSupport_coordinateDerivative hc i).mul_right
  · intro i
    exact integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      (hf.continuous.mul (hddcg i)) hc.mul_right
  · intro i
    exact integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      ((hf.continuous.mul (hdcg i)).mul (hdcφ i)) hc.mul_right.mul_right

theorem integral_mul_weightedDiffusion_of_hasCompactSupport_left {φ f g : Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 2 g)
    (hc : HasCompactSupport f) :
    (∫ x, f x * weightedDiffusion φ g x ∂potentialMeasure φ) =
      -(∫ x, inner ℝ (gradient f x) (gradient g x) ∂potentialMeasure φ) :=
  integral_mul_weightedDiffusion (hφ.differentiable (by norm_num))
    (hf.differentiable (by norm_num))
    (fun i => (contDiff_coordinateDerivative hg (m := 1) (by norm_num) i).differentiable
      (by norm_num)) (diffusionIntegrability_of_hasCompactSupport_left hφ hf hg hc)

lemma continuous_gradient_of_contDiff {f : Space n → ℝ} (hf : ContDiff ℝ 1 f) :
    Continuous (gradient f) :=
  (toDual ℝ (Space n)).symm.continuous.comp (hf.continuous_fderiv (by norm_num))

lemma hasCompactSupport_gradient {f : Space n → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (gradient f) :=
  (hf.fderiv ℝ).comp_left (map_zero (toDual ℝ (Space n)).symm)

lemma gradient_mul_real {f g : Space n → ℝ} {x : Space n}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    gradient (fun y => f y * g y) x = g x • gradient f x + f x • gradient g x := by
  ext i
  rw [← coordinateDerivative_eq_gradient, coordinateDerivative_mul hf hg]
  simp [coordinateDerivative_eq_gradient, mul_comm]

lemma cutoff_gradient_inner {χ h : Space n → ℝ}
    (hχ : Differentiable ℝ χ) (hh : Differentiable ℝ h) (x : Space n) :
    inner ℝ (gradient (fun y => χ y * χ y * h y) x) (gradient h x) =
      χ x ^ 2 * ‖gradient h x‖ ^ 2 +
        2 * (χ x * h x * inner ℝ (gradient χ x) (gradient h x)) := by
  rw [gradient_mul_real (f := fun y => χ y * χ y) ((hχ x).mul (hχ x)) (hh x),
    gradient_mul_real (hχ x) (hχ x)]
  simp only [inner_add_left, inner_smul_left, conj_trivial, real_inner_self_eq_norm_sq]
  ring

/-- Exact cutoff identity obtained by testing the actual harmonic equation with χ²h. -/
theorem weighted_harmonic_cutoff_identity {φ χ h : Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hχ : ContDiff ℝ 1 χ) (hh : ContDiff ℝ 2 h)
    (hc : HasCompactSupport χ) (hharm : ∀ x, weightedDiffusion φ h x = 0) :
    (∫ x, χ x ^ 2 * ‖gradient h x‖ ^ 2 ∂potentialMeasure φ) +
      2 * (∫ x, χ x * h x * inner ℝ (gradient χ x) (gradient h x) ∂potentialMeasure φ) = 0 := by
  have hgh := continuous_gradient_of_contDiff (hh.of_le (by norm_num))
  have hgχ := continuous_gradient_of_contDiff hχ
  have hE : Integrable (fun x => χ x ^ 2 * ‖gradient h x‖ ^ 2) (potentialMeasure φ) :=
    integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      ((hχ.continuous.pow 2).mul (hgh.norm.pow 2))
      (by simpa [pow_two, Pi.mul_def] using hc.mul_right.mul_right)
  have hC : Integrable (fun x => χ x * h x * inner ℝ (gradient χ x) (gradient h x))
      (potentialMeasure φ) :=
    integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      ((hχ.continuous.mul hh.continuous).mul (hgχ.inner hgh)) hc.mul_right.mul_right
  have hibp := integral_mul_weightedDiffusion_of_hasCompactSupport_left hφ
    ((hχ.mul hχ).mul (hh.of_le (by norm_num))) hh (hc.mul_right.mul_right)
  simp only [hharm, mul_zero, integral_zero] at hibp
  have hi : (∫ x, inner ℝ (gradient (fun y => χ y * χ y * h y) x) (gradient h x)
      ∂potentialMeasure φ) = 0 := neg_eq_zero.mp hibp.symm
  simp_rw [cutoff_gradient_inner (hχ.differentiable (by norm_num)) (hh.differentiable (by norm_num))] at hi
  rwa [integral_add hE (hC.const_mul 2), integral_const_mul] at hi

/-- Actual classical Caccioppoli inequality, without global gradient-integrability assumptions. -/
theorem weighted_caccioppoli {φ χ h : Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hχ : ContDiff ℝ 1 χ) (hh : ContDiff ℝ 2 h)
    (hc : HasCompactSupport χ) (hharm : ∀ x, weightedDiffusion φ h x = 0) :
    (∫ x, χ x ^ 2 * ‖gradient h x‖ ^ 2 ∂potentialMeasure φ) ≤
      4 * (∫ x, h x ^ 2 * ‖gradient χ x‖ ^ 2 ∂potentialMeasure φ) := by
  have hgh := continuous_gradient_of_contDiff (hh.of_le (by norm_num))
  have hgχ := continuous_gradient_of_contDiff hχ
  have hE : Integrable (fun x => χ x ^ 2 * ‖gradient h x‖ ^ 2) (potentialMeasure φ) :=
    integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      ((hχ.continuous.pow 2).mul (hgh.norm.pow 2))
      (by simpa [pow_two, Pi.mul_def] using hc.mul_right.mul_right)
  have hC : Integrable (fun x => χ x * h x * inner ℝ (gradient χ x) (gradient h x))
      (potentialMeasure φ) :=
    integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      ((hχ.continuous.mul hh.continuous).mul (hgχ.inner hgh)) hc.mul_right.mul_right
  have hB : Integrable (fun x => h x ^ 2 * ‖gradient χ x‖ ^ 2) (potentialMeasure φ) :=
    integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      ((hh.continuous.pow 2).mul (hgχ.norm.pow 2))
      (by simpa [pow_two, Pi.mul_def] using (hasCompactSupport_gradient hc).norm.mul_right.mul_left)
  have hpoint (x : Space n) :
      -(4 * (χ x * h x * inner ℝ (gradient χ x) (gradient h x))) ≤
        χ x ^ 2 * ‖gradient h x‖ ^ 2 + 4 * (h x ^ 2 * ‖gradient χ x‖ ^ 2) := by
    have hs := real_inner_self_nonneg (x := χ x • gradient h x + (2 * h x) • gradient χ x)
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      conj_trivial, real_inner_self_eq_norm_sq] at hs
    rw [real_inner_comm (gradient h x) (gradient χ x)] at hs
    rw [real_inner_comm (gradient h x) (gradient χ x)]
    nlinarith
  have hm := integral_mono ((hC.const_mul 4).neg) (hE.add (hB.const_mul 4)) hpoint
  simp only [Pi.neg_apply, Pi.add_apply] at hm
  rw [integral_neg, integral_const_mul, integral_add hE (hB.const_mul 4), integral_const_mul] at hm
  have hi := weighted_harmonic_cutoff_identity hφ hχ hh hc hharm
  linarith

end KLS
end

#print axioms KLS.diffusionIntegrability_of_hasCompactSupport_left
#print axioms KLS.integral_mul_weightedDiffusion_of_hasCompactSupport_left
#print axioms KLS.weighted_harmonic_cutoff_identity
#print axioms KLS.weighted_caccioppoli

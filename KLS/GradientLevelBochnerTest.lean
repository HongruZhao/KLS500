import KLS.SmoothUpperTest
import KLS.WeightedBochnerDomain

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology ContDiff ENNReal

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- The squared actual gradient is differentiable to the expected order. -/
theorem contDiff_gradient_norm_sq {f : Space n → ℝ} {k m : ℕ∞ω}
    (hf : ContDiff ℝ k f) (hm : m + 1 ≤ k) :
    ContDiff ℝ m (fun x => ‖gradient f x‖ ^ 2) := by
  have heq : (fun x => ‖gradient f x‖ ^ 2) =
      fun x => ∑ i : Fin n, coordinateDerivative f i x ^ 2 := by
    funext x
    simp only [EuclideanSpace.real_norm_sq_eq,coordinateDerivative_eq_gradient]
  rw [heq]
  exact ContDiff.sum fun i _ => (contDiff_coordinateDerivative hf hm i).pow 2

/-- Differentiating the literal squared gradient gives the Hessian-gradient contraction. -/
theorem coordinateDerivative_gradient_norm_sq {f : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) (j : Fin n) (x : Space n) :
    coordinateDerivative (fun y => ‖gradient f y‖ ^ 2) j x =
      2 * ∑ i : Fin n, coordinateDerivative f i x * coordinateHessian f x j i := by
  have heq : (fun y => ‖gradient f y‖ ^ 2) =
      fun y => ∑ i : Fin n, coordinateDerivative f i y * coordinateDerivative f i y := by
    funext y
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [coordinateDerivative_eq_gradient,pow_two]
  have hd (i : Fin n) :=
    (contDiff_coordinateDerivative hf (m := 1) (by norm_num) i).differentiable one_ne_zero x
  rw [heq,coordinateDerivative_sum
    (f := fun i y => coordinateDerivative f i y * coordinateDerivative f i y)
    (fun i => (hd i).mul (hd i)),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [coordinateDerivative_mul (hd i) (hd i)]
  change _ = 2 * (coordinateDerivative f i x * coordinateDerivative (coordinateDerivative f i) j x)
  ring

/-- The cutoff error obeys the actual product rule. -/
theorem bochnerCutoffError_mul {ζ η f : Space n → ℝ}
    (hζ : Differentiable ℝ ζ) (hη : Differentiable ℝ η) (x : Space n) :
    bochnerCutoffError (fun y => ζ y * η y) f x =
      η x * bochnerCutoffError ζ f x + ζ x * bochnerCutoffError η f x := by
  unfold bochnerCutoffError
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [coordinateDerivative_mul (hζ x) (hη x)]
  ring

/-- A monotone smooth level test of the actual squared gradient contributes
only a nonnegative term to the localized Bochner identity. -/
theorem bochnerCutoffError_gradient_level_nonneg {f : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) (a : ℝ) (x : Space n) :
    0 ≤ bochnerCutoffError (smoothUpperTest (fun y => ‖gradient f y‖ ^ 2) a) f x := by
  have hF : ContDiff ℝ 1 (fun y => ‖gradient f y‖ ^ 2) :=
    contDiff_gradient_norm_sq hf (by norm_num)
  unfold bochnerCutoffError
  rw [Finset.sum_comm]
  apply Finset.sum_nonneg
  intro j _
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum,coordinateDerivative_smoothUpperTest hF,
    coordinateDerivative_gradient_norm_sq hf]
  have hpos := Real.smoothTransition.monotone.deriv_nonneg (x := ‖gradient f x‖ ^ 2-a)
  have hs := mul_nonneg hpos (sq_nonneg
    (∑ i : Fin n, coordinateDerivative f i x * coordinateHessian f x j i))
  nlinarith only [hs]

/-- The monotone gradient-level multiplier adds no adverse error: only the
actual expanding-cutoff error remains, controlled by Hessian and gradient energy. -/
theorem bochnerCutoffError_gradient_level_cutoff_lower {f χ : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) (hχ : ContDiff ℝ 1 χ) (a : ℝ) (x : Space n) :
    -(‖gradient χ x‖ * (χ x ^ 2 * hessianSquare f x + ‖gradient f x‖ ^ 2)) ≤
      bochnerCutoffError
        (fun y => χ y ^ 2 * smoothUpperTest (fun z => ‖gradient f z‖ ^ 2) a y) f x := by
  let ψ := smoothUpperTest (fun y => ‖gradient f y‖ ^ 2) a
  have hψ : ContDiff ℝ 1 ψ := smoothUpperTest_contDiff
    (contDiff_gradient_norm_sq hf (by norm_num)) a
  have hψ0 : 0 ≤ ψ x := smoothUpperTest_nonneg _ _ _
  have hψ1 : ψ x ≤ 1 := Real.smoothTransition.le_one _
  have he := bochnerCutoffError_mul ((hχ.pow 2).differentiable one_ne_zero)
    (hψ.differentiable one_ne_zero) (f := f) x
  have hb := abs_bochnerCutoffError_sq_le_vanishing (hχ.differentiable one_ne_zero) (f := f) x
  have hp : |ψ x * bochnerCutoffError (fun y => χ y ^ 2) f x| ≤
      ‖gradient χ x‖ * (χ x ^ 2 * hessianSquare f x + ‖gradient f x‖ ^ 2) := by
    rw [abs_mul,abs_of_nonneg hψ0]
    exact (mul_le_of_le_one_left (abs_nonneg _) hψ1).trans hb
  have hn := mul_nonneg (sq_nonneg (χ x)) (bochnerCutoffError_gradient_level_nonneg hf a x)
  change 0 ≤ χ x ^ 2 * bochnerCutoffError ψ f x at hn
  rw [he]
  linarith [(abs_le.mp hp).1]

end KLS
end

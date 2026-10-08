import KLS.C11CenteredDifferenceCalculus
import KLS.HessianMetricComposition

open MeasureTheory Set Filter Matrix
open scoped ContDiff Topology NNReal ENNReal Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- The actual Hessian scalar-composition rule needs only the existing
 coordinate-gradient derivatives at the point. -/
theorem coordinateHessian_scalar_comp_at_C11
    {η : ℝ → ℝ} {f : Space n → ℝ} (hη : ContDiff ℝ 2 η)
    (hf : Differentiable ℝ f) {x : Space n}
    (hd : ∀ j, DifferentiableAt ℝ (coordinateDerivative f j) x) (i j : Fin n) :
    coordinateHessian (fun y => η (f y)) x i j =
      deriv (deriv η) (f x)*coordinateDerivative f i x*coordinateDerivative f j x +
        deriv η (f x)*coordinateHessian f x i j := by
  have hη' : ContDiff ℝ 1 (deriv η) :=
    (show ContDiff ℝ (1+1) η by convert hη using 1; norm_num).deriv'
  have hfirst : coordinateDerivative (fun y => η (f y)) j =
      fun y => deriv η (f y)*coordinateDerivative f j y := by
    funext y
    exact coordinateDerivative_scalar_comp (hη.differentiable (by norm_num) _) (hf y) j
  change coordinateDerivative (coordinateDerivative (fun y => η (f y)) j) i x = _
  rw [hfirst,coordinateDerivative_mul (f := fun y => deriv η (f y))
    (g := coordinateDerivative f j) ((hη'.differentiable (by norm_num) (f x)).comp x (hf x)) (hd j),
    coordinateDerivative_scalar_comp (hη'.differentiable (by norm_num) _) (hf x)]
  rfl

/-- Actual C1,1 scalar composition has the expected Hessian almost
 everywhere, without any classical C2 assumption on the original function. -/
theorem coordinateHessian_scalar_comp_ae_C11
    {η : ℝ → ℝ} {f : Space n → ℝ} {G : ℝ≥0}
    (hη : ContDiff ℝ 2 η) (hf : ContDiff ℝ 1 f) (hG : LipschitzWith G (gradient f)) :
    ∀ᵐ x ∂(volume : Measure (Space n)), ∀ i j,
      coordinateHessian (fun y => η (f y)) x i j =
        deriv (deriv η) (f x)*coordinateDerivative f i x*coordinateDerivative f j x +
          deriv η (f x)*coordinateHessian f x i j := by
  have hd : ∀ᵐ x ∂(volume : Measure (Space n)), ∀ j, DifferentiableAt ℝ (coordinateDerivative f j) x :=
    ae_all_iff.mpr (fun j => (lipschitz_coordinateDerivative_of_gradient_lipschitz hG j).ae_differentiableAt (μ := volume))
  filter_upwards [hd] with x hx
  exact coordinateHessian_scalar_comp_at_C11 hη (hf.differentiable (by norm_num)) hx

/-- The actual inverse-Hessian diffusion obeys scalar composition almost
 everywhere on an actual C1,1 input. No coefficient derivatives are used. -/
theorem hessianMetricDiffusion_scalar_comp_ae_C11
    (u V : Space n → ℝ) {η : ℝ → ℝ} {f : Space n → ℝ} {G : ℝ≥0}
    (hη : ContDiff ℝ 2 η) (hf : ContDiff ℝ 1 f) (hG : LipschitzWith G (gradient f)) :
    ∀ᵐ x ∂(volume : Measure (Space n)),
      hessianMetricDiffusion u V (fun y => η (f y)) x =
        deriv η (f x)*hessianMetricDiffusion u V f x +
          deriv (deriv η) (f x)*inverseHessianGradientForm u f x := by
  filter_upwards [coordinateHessian_scalar_comp_ae_C11 hη hf hG] with x hx
  unfold hessianMetricDiffusion inverseHessianGradientForm
  simp_rw [hx,coordinateDerivative_scalar_comp (hη.differentiable (by norm_num) _)
    (hf.differentiable (by norm_num) _),mul_add,Finset.sum_add_distrib,mul_sub,Finset.mul_sum]
  have hsecond : (∑ a, ∑ b, (coordinateHessian u x)⁻¹ a b *
      (deriv (deriv η) (f x)*coordinateDerivative f a x*coordinateDerivative f b x)) =
      ∑ a, ∑ b, deriv (deriv η) (f x) *
        ((coordinateHessian u x)⁻¹ a b*coordinateDerivative f a x*coordinateDerivative f b x) := by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  have hfirst : (∑ a, ∑ b, (coordinateHessian u x)⁻¹ a b *
      (deriv η (f x)*coordinateHessian f x a b)) =
      ∑ a, ∑ b, deriv η (f x)*((coordinateHessian u x)⁻¹ a b*coordinateHessian f x a b) := by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  have hdrift : (∑ a, coordinateDerivative V a (gradient u x) *
      (deriv η (f x)*coordinateDerivative f a x)) =
      ∑ a, deriv η (f x)*(coordinateDerivative V a (gradient u x)*coordinateDerivative f a x) := by
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [hsecond,hfirst,hdrift]
  ring

end KLS
end

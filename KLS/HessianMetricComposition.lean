import KLS.HessianMetricIntegration
import KLS.BrascampLiebDuality

/-! # Actual scalar composition calculus for the inverse-Hessian diffusion -/

open MeasureTheory InnerProductSpace Matrix
open scoped BigOperators ContDiff Matrix.Norms.Elementwise

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS

variable {n : ℕ}

lemma coordinateDerivative_scalar_comp {η : ℝ → ℝ} {f : Space n → ℝ} {x : Space n}
    (hη : DifferentiableAt ℝ η (f x)) (hf : DifferentiableAt ℝ f x) (i : Fin n) :
    coordinateDerivative (fun y => η (f y)) i x = deriv η (f x) * coordinateDerivative f i x := by
  have h := hη.hasDerivAt.comp_hasFDerivAt x hf.hasFDerivAt
  unfold coordinateDerivative
  simpa only [Function.comp_def, _root_.smul_apply, smul_eq_mul] using
    congrArg (fun D => D (EuclideanSpace.single i 1)) h.fderiv

lemma coordinateHessian_scalar_comp {η : ℝ → ℝ} {f : Space n → ℝ}
    (hη : ContDiff ℝ 2 η) (hf : ContDiff ℝ 2 f) (x : Space n) (i j : Fin n) :
    coordinateHessian (fun y => η (f y)) x i j =
      deriv (deriv η) (f x) * coordinateDerivative f i x * coordinateDerivative f j x +
        deriv η (f x) * coordinateHessian f x i j := by
  have hη' : ContDiff ℝ 1 (deriv η) :=
    (show ContDiff ℝ (1 + 1) η by convert hη using 1 <;> norm_num).deriv'
  have hf' : ContDiff ℝ 1 (coordinateDerivative f j) :=
    contDiff_coordinateDerivative hf (by norm_num) j
  have hfirst : coordinateDerivative (fun y => η (f y)) j =
      fun y => deriv η (f y) * coordinateDerivative f j y := by
    funext y
    exact coordinateDerivative_scalar_comp (hη.differentiable (by norm_num) _) (hf.differentiable (by norm_num) _) j
  change coordinateDerivative (coordinateDerivative (fun y => η (f y)) j) i x = _
  rw [hfirst, coordinateDerivative_mul
    (f := fun y => deriv η (f y)) (g := coordinateDerivative f j)
    ((hη'.comp (hf.of_le (by norm_num))).differentiable (by norm_num) x)
    (hf'.differentiable (by norm_num) x),
    coordinateDerivative_scalar_comp (hη'.differentiable (by norm_num) _) (hf.differentiable (by norm_num) _)]
  rfl

/-- The diffusion chain rule is derived for the actual coefficient field. -/
theorem hessianMetricDiffusion_scalar_comp (φ V : Space n → ℝ)
    {η : ℝ → ℝ} {f : Space n → ℝ} (hη : ContDiff ℝ 2 η) (hf : ContDiff ℝ 2 f)
    (x : Space n) :
    hessianMetricDiffusion φ V (fun y => η (f y)) x =
      deriv η (f x) * hessianMetricDiffusion φ V f x +
        deriv (deriv η) (f x) * inverseHessianGradientForm φ f x := by
  unfold hessianMetricDiffusion inverseHessianGradientForm
  simp_rw [coordinateHessian_scalar_comp hη hf,
    coordinateDerivative_scalar_comp (hη.differentiable (by norm_num) _) (hf.differentiable (by norm_num) _),
    mul_add, Finset.sum_add_distrib, mul_sub, Finset.mul_sum]
  have hsecond : (∑ a, ∑ b, (coordinateHessian φ x)⁻¹ a b *
      (deriv (deriv η) (f x) * coordinateDerivative f a x * coordinateDerivative f b x)) =
      ∑ a, ∑ b, deriv (deriv η) (f x) *
        ((coordinateHessian φ x)⁻¹ a b * coordinateDerivative f a x * coordinateDerivative f b x) := by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  have hfirst : (∑ a, ∑ b, (coordinateHessian φ x)⁻¹ a b *
      (deriv η (f x) * coordinateHessian f x a b)) =
      ∑ a, ∑ b, deriv η (f x) * ((coordinateHessian φ x)⁻¹ a b * coordinateHessian f x a b) := by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  have hdrift : (∑ a, coordinateDerivative V a (gradient φ x) *
      (deriv η (f x) * coordinateDerivative f a x)) =
      ∑ a, deriv η (f x) * (coordinateDerivative V a (gradient φ x) * coordinateDerivative f a x) := by
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [hsecond, hfirst, hdrift]
  ring

/-- An actual shifted potential, later shifted by its attained minimum. -/
def potentialHeight (φ : Space n → ℝ) (x₀ : Space n) (x : Space n) : ℝ :=
  φ x - φ x₀ + 1

lemma coordinateDerivative_potentialHeight (φ : Space n → ℝ) (x₀ x : Space n) (i : Fin n) :
    coordinateDerivative (potentialHeight φ x₀) i x = coordinateDerivative φ i x := by
  unfold potentialHeight coordinateDerivative
  rw [fderiv_add_const, fderiv_sub_const]

lemma coordinateHessian_potentialHeight (φ : Space n → ℝ) (x₀ x : Space n) :
    coordinateHessian (potentialHeight φ x₀) x = coordinateHessian φ x := by
  ext i j
  unfold coordinateHessian
  have hfun : coordinateDerivative (potentialHeight φ x₀) j = coordinateDerivative φ j :=
    funext (fun y => coordinateDerivative_potentialHeight φ x₀ y j)
  rw [hfun]

/-- The potential-height diffusion has no inverse-Hessian growth term. -/
theorem hessianMetricDiffusion_potentialHeight {φ : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    (V : Space n → ℝ) (x₀ x : Space n) :
    hessianMetricDiffusion φ V (potentialHeight φ x₀) x =
      (n : ℝ) - ∑ i, coordinateDerivative V i (gradient φ x) * coordinateDerivative φ i x := by
  unfold hessianMetricDiffusion
  rw [coordinateHessian_potentialHeight]
  simp_rw [coordinateDerivative_potentialHeight]
  rw [← trace_mul_hessian_eq_sum hφ, Matrix.nonsing_inv_mul _
    (isUnit_iff_ne_zero.mpr (hpos x).det_pos.ne')]
  simp

end KLS
end

#print axioms KLS.coordinateHessian_scalar_comp
#print axioms KLS.hessianMetricDiffusion_scalar_comp
#print axioms KLS.hessianMetricDiffusion_potentialHeight

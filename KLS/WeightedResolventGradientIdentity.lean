import KLS.GradientLevelDefect

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology ContDiff ENNReal RealInnerProductSpace

noncomputable section
namespace KLS
variable {n : ℕ}

/-- The literal resolvent equation identifies the gradient-diffusion pairing. -/
theorem gradient_diffusion_pairing_of_resolvent_equation {φ f g : Space n → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) {t : ℝ} (ht : 0 < t)
    (heq : ∀ x, f x-t*weightedDiffusion φ f x=g x) (x : Space n) :
    inner ℝ (gradient (weightedDiffusion φ f) x) (gradient f x) =
      t⁻¹ * (‖gradient f x‖ ^ 2-inner ℝ (gradient g x) (gradient f x)) := by
  have hfun : weightedDiffusion φ f = t⁻¹ • (f-g) := by
    funext y
    change weightedDiffusion φ f y = t⁻¹ * (f y-g y)
    rw [inv_mul_eq_div]
    apply (eq_div_iff ht.ne').2
    linarith [heq y]
  have hgrad : gradient (weightedDiffusion φ f) x =
      t⁻¹ • (gradient f x-gradient g x) := by
    ext i
    rw [← coordinateDerivative_eq_gradient,hfun,
      coordinateDerivative_smul
        ((hf.differentiable one_ne_zero x).sub (hg.differentiable one_ne_zero x))]
    change t⁻¹ * coordinateDerivative (fun y => f y-g y) i x = _
    rw [coordinateDerivative_sub (hf.differentiable one_ne_zero x)
      (hg.differentiable one_ne_zero x)]
    simp only [PiLp.smul_apply,PiLp.sub_apply,smul_eq_mul,coordinateDerivative_eq_gradient]
  rw [hgrad,inner_smul_left,inner_sub_left,real_inner_self_eq_norm_sq]
  simp only [conj_trivial]

end KLS
end

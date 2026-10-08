import OptVarianceEnergy
import Mathlib.Analysis.Calculus.Deriv.Comp

/-! Exact first and second derivatives after translating or reversing time. -/
open scoped ContDiff
noncomputable section
set_option maxHeartbeats 2000000
namespace KLS.ConstantReduction

theorem hasDerivAt_comp_affine {v : ℝ → ℝ} (hv : Differentiable ℝ v)
    (a b t : ℝ) : HasDerivAt (fun s : ℝ => v (a+b*s))
      (deriv v (a+b*t)*b) t := by
  have hline : HasDerivAt (fun s : ℝ => a+b*s) b t := by
    convert (hasDerivAt_const t a).add ((hasDerivAt_id t).const_mul b) using 1 <;>
      simp [funext_iff]
  exact (hv (a+b*t)).hasDerivAt.comp t hline

theorem deriv_comp_affine {v : ℝ → ℝ} (hv : Differentiable ℝ v)
    (a b t : ℝ) : deriv (fun s : ℝ => v (a+b*s)) t=deriv v (a+b*t)*b :=
  (hasDerivAt_comp_affine hv a b t).deriv

theorem secondDeriv_comp_affine {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v)
    (a b t : ℝ) : deriv (deriv (fun s : ℝ => v (a+b*s))) t=
      b^2*deriv (deriv v) (a+b*t) := by
  have heq : deriv (fun s : ℝ => v (a+b*s))=
      fun s : ℝ => deriv v (a+b*s)*b :=
    funext (deriv_comp_affine (hv.differentiable (by norm_num)) a b)
  rw [heq]
  rw [((hasDerivAt_comp_affine hv.differentiable_deriv_two a b t).mul_const b).deriv]
  ring

end KLS.ConstantReduction
end

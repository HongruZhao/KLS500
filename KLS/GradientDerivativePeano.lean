import KLS.PointwiseConvexHessian
import Mathlib.Analysis.Calculus.MeanValue

open Matrix Set Filter InnerProductSpace Asymptotics
open scoped Topology ContDiff Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- A derivative of the actual gradient supplies the genuine scalar Peano
 quadratic expansion. No neighborhood C2 hypothesis is needed. -/
theorem quadratic_peano_of_hasFDerivAt_gradient
    {u : Space n → ℝ} (hu : Differentiable ℝ u) {x : Space n}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (hg : HasFDerivAt (gradient u) (matrixAction A) x) :
    (fun y => u y - centeredQuadratic A x (gradient u x) (u x) y)
      =o[𝓝 x] (fun y => ‖y-x‖^2) := by
  let q := centeredQuadratic A x (gradient u x) (u x)
  let f := fun y => u y-q y
  let F := fun y => fderiv ℝ u y - fderiv ℝ q y
  have hder (y : Space n) : HasFDerivAt f (F y) y :=
    (hu y).hasFDerivAt.sub ((differentiable_centeredQuadratic A x (gradient u x) (u x)) y).hasFDerivAt
  have hsecond := (toDual ℝ (Space n)).toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp x hg
  change HasFDerivAt (fun y => (toDual ℝ (Space n)) (gradient u y)) (matrixFrechetHessian A) x at hsecond
  simp only [toDual_gradient] at hsecond
  have heq (y : Space n) : fderiv ℝ q y = fderiv ℝ u x + matrixFrechetHessian A (y-x) := by
    rw [← toDual_gradient,← toDual_gradient]
    simp only [q,gradient_centeredQuadratic_of_isSymm hA,map_add,matrixFrechetHessian,
      ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe]
    rfl
  have hsmall : F =o[𝓝 x] (fun y => ‖y-x‖^1) := by
    have hh := hsecond.isLittleO.norm_right
    simpa only [F,heq,sub_add_eq_sub_sub,pow_one] using hh
  have hh := convex_univ.isLittleO_pow_succ (x₀ := x) (n := 1) (mem_univ x)
    (fun y _ => (hder y).hasFDerivWithinAt) (by simpa using hsmall)
  simpa only [f,q,centeredQuadratic_center,sub_self,sub_zero,nhdsWithin_univ] using hh

end KLS
end

import KLS.WeakMomentLocalInverseControl
import KLS.MatrixFrechetHessian
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

open Matrix Set Filter InnerProductSpace
open scoped Topology ContDiff Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- A derivative of the actual gradient supplies the actual second Frechet
 derivative, without continuity of second derivatives in a neighborhood. -/
theorem differentiableAt_fderiv_of_gradient
    {u : Space n → ℝ} {x : Space n} (hg : DifferentiableAt ℝ (gradient u) x) :
    DifferentiableAt ℝ (fderiv ℝ u) x := by
  have hh := (toDual ℝ (Space n)).toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp x hg.hasFDerivAt
  change HasFDerivAt (fun y => (toDual ℝ (Space n)) (gradient u y)) _ x at hh
  simpa only [toDual_gradient] using hh.differentiableAt

/-- At a point where the gradient is differentiable, the actual coordinate
 Hessian is symmetric; first differentiability of u is required nearby. -/
theorem coordinateHessian_isSymm_of_gradient_differentiableAt
    {u : Space n → ℝ} (hu : Differentiable ℝ u) {x : Space n}
    (hg : DifferentiableAt ℝ (gradient u) x) : (coordinateHessian u x).IsSymm := by
  have hdd := differentiableAt_fderiv_of_gradient hg
  apply Matrix.IsSymm.ext
  intro i j
  simp only [coordinateHessian_eq_fderiv_fderiv hdd]
  exact second_derivative_symmetric (fun y => (hu y).hasFDerivAt) hdd.hasFDerivAt _ _

set_option synthInstance.maxHeartbeats 100000 in
-- Coordinate projections require extra instance elaboration through Euclidean space.
/-- The derivative of the actual gradient agrees with the actual coordinate
 Hessian whenever that derivative exists. -/
theorem hasFDerivAt_gradient_of_differentiableAt_gradient
    {u : Space n → ℝ} (hu : Differentiable ℝ u) {x : Space n}
    (hg : DifferentiableAt ℝ (gradient u) x) :
    HasFDerivAt (gradient u) (matrixAction (coordinateHessian u x)) x := by
  have hsym := coordinateHessian_isSymm_of_gradient_differentiableAt hu hg
  have hentry (i j : Fin n) : coordinateHessian u x i j =
      (fderiv ℝ (gradient u) x (EuclideanSpace.single i 1)) j := by
    have heq : coordinateDerivative u j = fun y : Space n => gradient u y j := by
      funext y
      exact coordinateDerivative_eq_gradient u j y
    change coordinateDerivative (coordinateDerivative u j) i x = _
    rw [heq]
    have hd : HasFDerivAt (fun y : Space n => gradient u y j)
        ((EuclideanSpace.proj (𝕜 := ℝ) j).comp (fderiv ℝ (gradient u) x)) x :=
      (EuclideanSpace.proj (𝕜 := ℝ) j).hasFDerivAt.comp x hg.hasFDerivAt
    rw [coordinateDerivative,hd.fderiv]
    rfl
  have heq : matrixAction (coordinateHessian u x) = fderiv ℝ (gradient u) x := by
    apply ContinuousLinearMap.ext
    intro v
    have hv : (∑ j : Fin n, v j • (EuclideanSpace.single j 1)) = v := by
      ext i
      simp [Pi.single_apply]
    have hsum : fderiv ℝ (gradient u) x v =
        ∑ j : Fin n, v j • (fderiv ℝ (gradient u) x (EuclideanSpace.single j 1)) := by
      conv_lhs => rw [← hv]
      simp only [map_sum,map_smul]
    rw [hsum]
    ext i
    simp only [matrixAction_apply,WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [← hentry j i,hsym.apply j i]
    ring
  exact heq ▸ hg.hasFDerivAt

end KLS
end

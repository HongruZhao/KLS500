import KLS.LocalHessianGradientDerivative

open Matrix InnerProductSpace
open scoped ContDiff Topology Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- The coordinate Hessian, realized as the derivative of the actual Frechet derivative. -/
def matrixFrechetHessian (A : Matrix (Fin n) (Fin n) ℝ) :
    Space n →L[ℝ] Space n →L[ℝ] ℝ :=
  (toDual ℝ (Space n)).toContinuousLinearEquiv.toContinuousLinearMap.comp (matrixAction A)

def matrixFrechetHessianParameterCLM :
    Matrix (Fin n) (Fin n) ℝ →L[ℝ] (Space n →L[ℝ] Space n →L[ℝ] ℝ) :=
  ({ toFun := matrixFrechetHessian
     map_add' := fun A B => by
       apply ContinuousLinearMap.ext
       intro v
       simp [matrixFrechetHessian, matrixAction_add_matrices]
     map_smul' := fun r A => by
       apply ContinuousLinearMap.ext
       intro v
       simp [matrixFrechetHessian, matrixAction_smul_scalar] } :
    Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] (Space n →L[ℝ] Space n →L[ℝ] ℝ)).toContinuousLinearMap

@[simp] theorem matrixFrechetHessianParameterCLM_apply (A : Matrix (Fin n) (Fin n) ℝ) :
    matrixFrechetHessianParameterCLM A = matrixFrechetHessian A := rfl

theorem hasFDerivAt_fderiv_of_contDiffAt_two {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ 2 u x) :
    HasFDerivAt (fderiv ℝ u) (matrixFrechetHessian (coordinateHessian u x)) x := by
  have h := (toDual ℝ (Space n)).toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp x
    (hasFDerivAt_gradient_of_contDiffAt_two hu)
  change HasFDerivAt (fun y => (toDual ℝ (Space n)) (gradient u y))
    (matrixFrechetHessian (coordinateHessian u x)) x at h
  simpa only [toDual_gradient] using h

theorem norm_matrixFrechetHessian_sub_le (A B : Matrix (Fin n) (Fin n) ℝ) :
    ‖matrixFrechetHessian A - matrixFrechetHessian B‖ ≤
      ‖matrixFrechetHessianParameterCLM (n := n)‖ * ‖A - B‖ := by
  simpa only [map_sub, matrixFrechetHessianParameterCLM_apply] using
    (matrixFrechetHessianParameterCLM (n := n)).le_opNorm (A - B)

theorem actual_frechet_hessian_holder_of_coordinate_holder
    {u : Space n → ℝ} {S : Set (Space n)} {M γ : ℝ}
    (hHol : ∀ x ∈ S, ∀ y ∈ S,
      ‖coordinateHessian u x - coordinateHessian u y‖ ≤ M * ‖x - y‖ ^ γ) :
    ∀ x ∈ S, ∀ y ∈ S,
      ‖matrixFrechetHessian (coordinateHessian u x) -
        matrixFrechetHessian (coordinateHessian u y)‖ ≤
      (‖matrixFrechetHessianParameterCLM (n := n)‖ * M) * ‖x - y‖ ^ γ := by
  intro x hx y hy
  exact (norm_matrixFrechetHessian_sub_le _ _).trans <| by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hHol x hx y hy) (norm_nonneg _)

end KLS
end

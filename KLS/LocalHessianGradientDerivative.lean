import KLS.WeightedPerturbativeLinearization

open MeasureTheory Matrix Set Filter Metric InnerProductSpace Asymptotics
open scoped ContDiff Topology BigOperators Matrix.Norms.Elementwise NNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
namespace KLS
variable {n : ℕ}

lemma hasFDerivAt_gradient_of_contDiffAt_two {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ 2 u x) :
    HasFDerivAt (gradient u) (matrixAction (coordinateHessian u x)) x := by
  have hg : DifferentiableAt ℝ (gradient u) x :=
    ((toDual ℝ (Space n)).symm.toContinuousLinearEquiv.contDiff.contDiffAt.comp x
      (hu.fderiv_right (m := 1) (by norm_num))).differentiableAt (by norm_num)
  have hsym := coordinateHessian_isSymm_of_contDiffAt hu
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
    rw [coordinateDerivative, hd.fderiv]
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
      simp only [map_sum, map_smul]
    rw [hsum]
    ext i
    simp only [matrixAction_apply, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [← hentry j i, hsym.apply j i]
    ring
  exact heq ▸ hg.hasFDerivAt

def matrixActionParameterCLM : Matrix (Fin n) (Fin n) ℝ →L[ℝ] (Space n →L[ℝ] Space n) :=
  ({ toFun := matrixAction
     map_add' := fun A B => by
       apply ContinuousLinearMap.ext
       intro v
       exact matrixAction_add_matrices A B v
     map_smul' := fun r A => by
       apply ContinuousLinearMap.ext
       intro v
       exact matrixAction_smul_scalar r A v } :
    Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] (Space n →L[ℝ] Space n)).toContinuousLinearMap

@[simp] lemma matrixActionParameterCLM_apply (A : Matrix (Fin n) (Fin n) ℝ) :
    matrixActionParameterCLM A = matrixAction A := rfl

end KLS
end

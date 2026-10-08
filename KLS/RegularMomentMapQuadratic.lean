import KLS.GaussianMomentMapLimit
import KLS.HessianTraceBoundedGradient
import KLS.SymmetricMatrixApproximation

/-!
# The quadratic estimate from a genuine regular bounded moment map

The moment map, Monge--Ampere equation and Hessian bound remain explicit.
The Gaussian-added Stein argument, actual tensor/trace estimate and spectral
transport supply the constant eight. Singular and indefinite symmetric
quadratics are included. This does not assert moment-map existence.
-/

open MeasureTheory ProbabilityTheory InnerProductSpace Matrix Set
open scoped ContDiff Matrix.Norms.Elementwise
noncomputable section
namespace KLS

variable {n : ℕ}

lemma continuous_matrixAction :
    Continuous (matrixAction : Matrix (Fin n) (Fin n) ℝ → (Space n →L[ℝ] Space n)) := by
  let F : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] (Space n →L[ℝ] Space n) :=
    { toFun := matrixAction
      map_add' := by
        intro A B
        ext x i
        simp [matrixAction_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro c A
        ext x i
        simp [matrixAction_apply, Finset.mul_sum, mul_assoc] }
  exact F.continuous_of_finiteDimensional

lemma exists_bound_fderiv_gradient_of_bounded_hessian {φ : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ)
    (hH : Bornology.IsBounded (range (coordinateHessian φ))) :
    ∃ L : ℝ, ∀ x, ‖fderiv ℝ (gradient φ) x‖ ≤ L := by
  obtain ⟨L, hL⟩ := exists_bound_matrix_comp_of_bounded_range hH
    continuous_matrixAction.norm
  refine ⟨L, fun x => ?_⟩
  have he : matrixAction (coordinateHessian φ x) = fderiv ℝ (gradient φ) x := by
    rw [← momentMap_hessianMatrix_eq_coordinateHessian hφ x]
    apply ContinuousLinearMap.ext
    intro v
    exact MomentMap.matrixAction_hessianMatrix_apply
      ((MomentMap.contDiff_gradient_of_contDiff_two hφ).differentiable (by norm_num)) x v
  simpa only [he, norm_norm] using hL x

theorem quadraticVarianceEight_of_regular_bounded_momentMap
    {μ : Measure (Space n)} {φ V : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hμ : admissibleMeasure μ) (hc : IsCompact μ.support)
    (hφ : ContDiff ℝ 4 φ) (hV : ContDiff ℝ 2 V)
    (hφconv : ConvexOn ℝ univ φ) (hVconv : ConvexOn ℝ univ V)
    (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    (hMA : ∀ x, Real.log (coordinateHessian φ x).det = -φ x + V (gradient φ x))
    (hH : Bornology.IsBounded (range (coordinateHessian φ)))
    (hgrad : Bornology.IsBounded (range (gradient φ)))
    (hpush : MomentMap.gradientPushforward φ = μ) :
    QuadraticVarianceEight μ := by
  let : IsProbabilityMeasure μ := hμ.isProb
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by norm_num)
  obtain ⟨L, hL⟩ := exists_bound_fderiv_gradient_of_bounded_hessian hφ2 hH
  have hiso : IsIsotropic (MomentMap.gradientPushforward φ) := by
    simpa only [hpush] using hμ.isotropic
  apply hμ.logConcave.quadraticVarianceEight_of_invertible
  intro M hM hMdet
  obtain ⟨A, U, B, _, hU, hBsym, horth, hAA, hpull, hnorm⟩ :=
    exists_spectral_quadratic_transport M hM
  have hA : A.det ≠ 0 := by
    intro hz
    apply hMdet
    rw [← hpull, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hz]
    ring
  have hB : B.PosSemidef := by
    rw [← hAA]
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self A
  have htrace := integral_hessianTraceSquare_le_two_trace_of_bounded_gradient
    hφ hV hφconv hVconv hpos hMA hH hgrad hiso hB
  have hstein := quadratic_variance_le_hessian_contraction_of_compact_target
    hμ hc hφ2 hpush hL M A U hA hU horth hpull
  simp only [hAA, momentMap_hessianMatrix_eq_coordinateHessian hφ2] at hstein
  change ProbabilityTheory.variance (matrixQuadratic M) μ ≤
    4 * (∫ x, hessianTraceSquare φ B x ∂potentialMeasure φ) at hstein
  rw [← matrixFrobeniusSq_eq_trace_sq hBsym, hnorm] at htrace
  linarith

end KLS
end

#print axioms KLS.exists_bound_fderiv_gradient_of_bounded_hessian
#print axioms KLS.quadraticVarianceEight_of_regular_bounded_momentMap

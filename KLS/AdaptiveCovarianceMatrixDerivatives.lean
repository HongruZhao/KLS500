import KLS.AdaptiveStandardizedMoments
import KLS.MatrixLogDetSecond

/-! Matrix derivatives of the actual covariance field and its actual noise. -/
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped Topology BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS.AdaptiveLocalization
open KLS.MatrixCalculus
variable {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

def coordinateCovarianceMatrix (μ : Measure (Space n)) (z : Fin (n+n*n) → ℝ) :
    Matrix (Fin n) (Fin n) ℝ := covariance μ (decodeState z).1 (decodeState z).2

def covarianceNoiseMatrix (μ : Measure (Space n)) (k : Fin n) (z : Fin (n+n*n) → ℝ) :
    Matrix (Fin n) (Fin n) ℝ := fun i j => covarianceNoiseCoefficient μ i j k z

theorem contDiff_coordinateCovarianceMatrix (hμ : IsCompact μ.support) :
    ContDiff ℝ (⊤ : ℕ∞) (coordinateCovarianceMatrix μ) :=
  (contDiff_covariance_matrix hμ).comp contDiff_decodeState

theorem coordinateCovarianceMatrix_posDef (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (z : Fin (n+n*n) → ℝ) :
    (coordinateCovarianceMatrix μ z).PosDef := covariance_posDef hμ hfull (decodeState z)

theorem fderiv_coordinateCovarianceMatrix_apply (hμ : IsCompact μ.support)
    (z v : Fin (n+n*n) → ℝ) (i j : Fin n) :
    fderiv ℝ (coordinateCovarianceMatrix μ) z v i j = coordinateCovarianceGradient μ i j z v := by
  exact (fderiv_matrix_entry ((contDiff_coordinateCovarianceMatrix hμ).differentiable (by simp) z) i j v).symm

theorem fderiv_coordinateCovarianceMatrix_diffusion (hμ : IsCompact μ.support)
    (z : Fin (n+n*n) → ℝ) (k : Fin n) :
    fderiv ℝ (coordinateCovarianceMatrix μ) z (coordinateDiffusion μ k z) = covarianceNoiseMatrix μ k z := by
  ext i j
  exact fderiv_coordinateCovarianceMatrix_apply hμ z _ i j

theorem fderiv_fderiv_coordinateCovarianceMatrix_apply (hμ : IsCompact μ.support)
    (z u v : Fin (n+n*n) → ℝ) (i j : Fin n) :
    fderiv ℝ (fun w => fderiv ℝ (coordinateCovarianceMatrix μ) w v) z u i j =
      coordinateCovarianceHessian μ i j z u v := by
  have hA : DifferentiableAt ℝ (fun w => fderiv ℝ (coordinateCovarianceMatrix μ) w v) z :=
    (((contDiff_coordinateCovarianceMatrix hμ).fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable
      (by simp) z).clm_apply (differentiableAt_const v)
  rw [← fderiv_matrix_entry hA i j u]
  simp_rw [fderiv_coordinateCovarianceMatrix_apply hμ]
  rw [fderiv_clm_apply ((contDiff_coordinateCovarianceGradient hμ i j).differentiable (by simp) z)
    (differentiableAt_const v)]
  simp [coordinateCovarianceHessian, ContinuousLinearMap.add_apply, ContinuousLinearMap.flip_apply]

/-- The actual covariance matrix field has matrix generator minus itself. -/
theorem coordinateCovarianceMatrix_generator (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (z : Fin (n+n*n) → ℝ) :
    fderiv ℝ (coordinateCovarianceMatrix μ) z (coordinateDrift μ z) +
      (1/2 : ℝ) • ∑ k : Fin n, fderiv ℝ
        (fun w => fderiv ℝ (coordinateCovarianceMatrix μ) w (coordinateDiffusion μ k z)) z
        (coordinateDiffusion μ k z) = -coordinateCovarianceMatrix μ z := by
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, Matrix.neg_apply, smul_eq_mul]
  simp_rw [fderiv_coordinateCovarianceMatrix_apply hμ, fderiv_fderiv_coordinateCovarianceMatrix_apply hμ]
  exact coordinateCovariance_generator hμ hfull i j z

end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.coordinateCovarianceMatrix_generator

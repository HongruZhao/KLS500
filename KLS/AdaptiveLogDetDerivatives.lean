import KLS.AdaptiveCovarianceMatrixDerivatives

/-! Actual first and second derivatives of the log determinant of covariance. -/
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped Topology BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS.AdaptiveLocalization
open KLS.MatrixCalculus
variable {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

def coordinateLogDet (μ : Measure (Space n)) (z : Fin (n+n*n) → ℝ) : ℝ :=
  Real.log (coordinateCovarianceMatrix μ z).det

def coordinateLogDetGradient (μ : Measure (Space n)) :
    (Fin (n+n*n) → ℝ) → (Fin (n+n*n) → ℝ) →L[ℝ] ℝ := fderiv ℝ (coordinateLogDet μ)

def coordinateLogDetHessian (μ : Measure (Space n)) :
    (Fin (n+n*n) → ℝ) → (Fin (n+n*n) → ℝ) →L[ℝ] (Fin (n+n*n) → ℝ) →L[ℝ] ℝ :=
  fderiv ℝ (coordinateLogDetGradient μ)

theorem contDiff_coordinateLogDet (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) : ContDiff ℝ (⊤ : ℕ∞) (coordinateLogDet μ) :=
  ((contDiff_det.of_le (by simp)).comp (contDiff_coordinateCovarianceMatrix hμ)).log
    (fun z => (coordinateCovarianceMatrix_posDef hμ hfull z).det_pos.ne')

theorem contDiff_coordinateLogDetGradient (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) : ContDiff ℝ (⊤ : ℕ∞) (coordinateLogDetGradient μ) :=
  (contDiff_coordinateLogDet hμ hfull).fderiv_right (m := (⊤ : ℕ∞)) (by simp)

theorem coordinateLogDetGradient_apply (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (z v : Fin (n+n*n) → ℝ) :
    coordinateLogDetGradient μ z v =
      ((coordinateCovarianceMatrix μ z)⁻¹ * fderiv ℝ (coordinateCovarianceMatrix μ) z v).trace :=
  fderiv_logDet_comp_apply_posDef ((contDiff_coordinateCovarianceMatrix hμ).differentiable (by simp) z)
    (coordinateCovarianceMatrix_posDef hμ hfull z) v

theorem coordinateLogDetHessian_apply (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (z u v : Fin (n+n*n) → ℝ) :
    coordinateLogDetHessian μ z u v =
      ((coordinateCovarianceMatrix μ z)⁻¹ *
        fderiv ℝ (fun w => fderiv ℝ (coordinateCovarianceMatrix μ) w v) z u).trace -
      ((coordinateCovarianceMatrix μ z)⁻¹ * fderiv ℝ (coordinateCovarianceMatrix μ) z u *
        (coordinateCovarianceMatrix μ z)⁻¹ * fderiv ℝ (coordinateCovarianceMatrix μ) z v).trace := by
  have h := fderiv_fderiv_logDet_comp_apply_posDef
    ((contDiff_coordinateCovarianceMatrix hμ).of_le (by simp))
    (coordinateCovarianceMatrix_posDef hμ hfull z) v u
  have he : fderiv ℝ (fun w => coordinateLogDetGradient μ w v) z u =
      coordinateLogDetHessian μ z u v := by
    rw [fderiv_clm_apply ((contDiff_coordinateLogDetGradient hμ hfull).differentiable (by simp) z)
      (differentiableAt_const v)]
    simp [coordinateLogDetHessian, ContinuousLinearMap.add_apply, ContinuousLinearMap.flip_apply]
  change fderiv ℝ (fun w => coordinateLogDetGradient μ w v) z u = _ at h
  rwa [he] at h

theorem coordinateLogDet_noise (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (z : Fin (n+n*n) → ℝ) (k : Fin n) :
    coordinateLogDetGradient μ z (coordinateDiffusion μ k z) =
      ((coordinateCovarianceMatrix μ z)⁻¹ * covarianceNoiseMatrix μ k z).trace := by
  rw [coordinateLogDetGradient_apply hμ hfull, fderiv_coordinateCovarianceMatrix_diffusion hμ]

end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.coordinateLogDetHessian_apply
#print axioms KLS.AdaptiveLocalization.coordinateLogDet_noise

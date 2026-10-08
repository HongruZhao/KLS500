import KLS.AdaptiveLogDetDerivatives

/-! Exact generator and Brownian coefficients of the covariance log determinant. -/
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped Topology BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS.AdaptiveLocalization
open LevyStochCalc KLS.LocalDiffusion
variable {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

def logDetTraceCorrection (μ : Measure (Space n)) (z : Fin (n+n*n) → ℝ) : ℝ :=
  ∑ k : Fin n, ((coordinateCovarianceMatrix μ z)⁻¹ * covarianceNoiseMatrix μ k z *
    (coordinateCovarianceMatrix μ z)⁻¹ * covarianceNoiseMatrix μ k z).trace

def logDetNoiseCoefficient (μ : Measure (Space n)) (k : Fin n) (z : Fin (n+n*n) → ℝ) : ℝ :=
  ((coordinateCovarianceMatrix μ z)⁻¹ * covarianceNoiseMatrix μ k z).trace

/-- The actual log-determinant generator is minus dimension minus the genuine
half trace contraction of the covariance noise. No process differential is assumed. -/
theorem coordinateLogDet_generator (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (z : Fin (n+n*n) → ℝ) :
    coordinateLogDetGradient μ z (coordinateDrift μ z) +
      1/2 * ∑ k : Fin n, coordinateLogDetHessian μ z
        (coordinateDiffusion μ k z) (coordinateDiffusion μ k z) =
      -(n : ℝ) - 1/2 * logDetTraceCorrection μ z := by
  have hh := congrArg (fun B : Matrix (Fin n) (Fin n) ℝ =>
    ((coordinateCovarianceMatrix μ z)⁻¹ * B).trace)
    (coordinateCovarianceMatrix_generator hμ hfull z)
  simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_sum, Matrix.trace_add,
    Matrix.trace_smul, Matrix.trace_sum, smul_eq_mul, Matrix.mul_neg, Matrix.trace_neg] at hh
  rw [Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr
    (coordinateCovarianceMatrix_posDef hμ hfull z).det_pos.ne'), Matrix.trace_one, Fintype.card_fin] at hh
  rw [coordinateLogDetGradient_apply hμ hfull]
  simp_rw [coordinateLogDetHessian_apply hμ hfull, fderiv_coordinateCovarianceMatrix_diffusion hμ]
  rw [Finset.sum_sub_distrib]
  unfold logDetTraceCorrection
  linarith

/-- The exact coordinate generator consumed by the genuine local Itô theorem. -/
theorem observableGenerator_coordinateLogDet (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (z : Fin (n+n*n) → ℝ) :
    observableGenerator (coordinateDrift μ) (coordinateDiffusion μ)
      (coordinateLogDetGradient μ) (coordinateLogDetHessian μ) z =
      -(n : ℝ) - 1/2 * logDetTraceCorrection μ z := by
  have h := coordinateLogDet_generator hμ hfull z
  rw [apply_eq_sum_coordDeriv] at h
  simp_rw [apply₂_eq_sum_coordDeriv₂] at h
  unfold observableGenerator
  have hd : (∑ a : Fin (n+n*n), coordDeriv (coordinateLogDetGradient μ) a z * coordinateDrift μ z a) =
      ∑ a : Fin (n+n*n), coordinateDrift μ z a * coordDeriv (coordinateLogDetGradient μ) a z :=
    Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [hd]
  convert h using 1
  congr 1
  congr 1
  simp_rw [Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro k _
  ring

end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.coordinateLogDet_generator
#print axioms KLS.AdaptiveLocalization.observableGenerator_coordinateLogDet

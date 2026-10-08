import KLS.WeakWeightedMean
import KLS.WeakHessianCompactTest
import KLS.HessianMatrixMean

open MeasureTheory ProbabilityTheory InnerProductSpace Set Filter Matrix
open scoped BigOperators ContDiff Topology ENNReal NNReal Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

theorem memLp_actual_hessian_entry_of_global_gradient_lipschitz
    {φ : Space n → ℝ} {G : ℝ≥0} {μ : Measure (Space n)} [IsFiniteMeasure μ]
    (hG : LipschitzWith G (gradient φ)) (i j : Fin n) (p : ℝ≥0∞) :
    MemLp (fun x => coordinateHessian φ x i j) p μ :=
  MemLp.of_bound (measurable_coordinateDerivative (coordinateDerivative φ j) i).aestronglyMeasurable G
    (Eventually.of_forall fun x => actual_hessian_global_entry_bound hG x i j)

/-- The mean of the actual almost-everywhere Hessian follows from the
isotropic gradient pushforward at the original C1,1 source regularity. -/
theorem integral_actual_hessian_entry_eq_one_C11
    {φ : Space n → ℝ} {G : ℝ≥0} [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 1 φ) (hG : LipschitzWith G (gradient φ))
    (hiso : IsIsotropic (MomentMap.gradientPushforward φ)) (i j : Fin n) :
    (∫ x, coordinateHessian φ x i j ∂potentialMeasure φ) =
      (1 : Matrix (Fin n) (Fin n) ℝ) i j := by
  have hgm : AEMeasurable (gradient φ) (potentialMeasure φ) :=
    hG.continuous.measurable.aemeasurable
  have hf : Integrable (coordinateDerivative φ j) (potentialMeasure φ) := by
    change Integrable (fun x => coordinateDerivative φ j x) (potentialMeasure φ)
    simpa only [coordinateDerivative_eq_gradient] using
      MomentMap.integrable_gradient_coordinate hgm hiso j
  have hF := (memLp_actual_hessian_entry_of_global_gradient_lipschitz
    (μ := potentialMeasure φ) hG i j 2).integrable (by norm_num)
  have hfd : Integrable (fun x => coordinateDerivative φ j x * coordinateDerivative φ i x)
      (potentialMeasure φ) := by
    simpa only [coordinateDerivative_eq_gradient] using
      MomentMap.integrable_gradient_coordinate_mul hgm hiso j i
  rw [integral_raw_derivative_potential hφ
    (actual_hessian_hasLocalWeakCoordinateDerivative hG.locallyLipschitz i j) hf hF hfd]
  simp_rw [coordinateDerivative_eq_gradient]
  simpa only [Matrix.one_apply, eq_comm] using MomentMap.integral_gradient_coordinate_mul hgm hiso j i

end KLS
end

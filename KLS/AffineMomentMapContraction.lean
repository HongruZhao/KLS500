import KLS.AffineMomentMapStein

/-!
# Integrated actual transported Hessian contraction

C2 source smoothness gives the symmetry of the genuine coordinate Hessian.
The affine Stein derivative energies are integrable, so their finite sum
equals the integral of the literal noncommuting trace contraction.
-/

open MeasureTheory ProbabilityTheory InnerProductSpace Matrix Set Filter
open scoped BigOperators ContDiff

noncomputable section
namespace KLS
namespace MomentMap

variable {n : ℕ}

theorem contDiff_gradient_of_contDiff_two {φ : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) : ContDiff ℝ 1 (gradient φ) := by
  exact (toDual ℝ (Space n)).symm.toContinuousLinearEquiv.contDiff.comp
    (hφ.fderiv_right (m := 1) (by norm_num))

theorem hessianMatrix_eq_coordinateHessian_transpose (φ : Space n → ℝ) (x : Space n) :
    hessianMatrix φ x = (coordinateHessian φ x).transpose := by
  ext i j
  simp only [hessianMatrix, Matrix.transpose_apply, coordinateHessian]
  have heq : (fun y => gradient φ y i) = coordinateDerivative φ i := by
    funext y
    exact (coordinateDerivative_eq_gradient φ i y).symm
  rw [heq]
  rfl

theorem hessianMatrix_isSymm {φ : Space n → ℝ} (hφ : ContDiff ℝ 2 φ) (x : Space n) :
    (hessianMatrix φ x).IsSymm := by
  rw [hessianMatrix_eq_coordinateHessian_transpose,
    (coordinateHessian_symmetric hφ x).eq]
  exact coordinateHessian_symmetric hφ x

/-- Each actual transported derivative energy is integrable. -/
theorem integrable_transportedGradientDerivative_sq {φ : Space n → ℝ}
    [IsFiniteMeasure (potentialMeasure φ)] (hφ : ContDiff ℝ 2 φ)
    {B : ℝ} (hB : ∀ x, ‖fderiv ℝ (gradient φ) x‖ ≤ B)
    (A : Matrix (Fin n) (Fin n) ℝ) (w : Space n) :
    Integrable (fun x => ‖transportedGradientDerivative φ A x w‖ ^ 2)
      (potentialMeasure φ) :=
  (memLp_transportedGradientDerivative (contDiff_gradient_of_contDiff_two hφ) hB A w).norm.integrable_sq

/-- Exact integral contraction. Integrability is proved before interchanging
the sum and integral. The Hessian is the actual derivative matrix of phi. -/
theorem sum_integral_transportedGradientDerivative_sq {φ : Space n → ℝ}
    [IsFiniteMeasure (potentialMeasure φ)] (hφ : ContDiff ℝ 2 φ)
    {B : ℝ} (hB : ∀ x, ‖fderiv ℝ (gradient φ) x‖ ≤ B)
    (A U : Matrix (Fin n) (Fin n) ℝ) (hU : U.transpose * U = 1) :
    (∑ i : Fin n, ∫ x, ‖transportedGradientDerivative φ A x (WithLp.toLp 2 (U i))‖ ^ 2
      ∂potentialMeasure φ) =
      ∫ x, (A.transpose * A * hessianMatrix φ x * (A.transpose * A) * hessianMatrix φ x).trace
        ∂potentialMeasure φ := by
  rw [← integral_finsetSum Finset.univ
    (fun i _ => integrable_transportedGradientDerivative_sq hφ hB A (WithLp.toLp 2 (U i)))]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => sum_transportedGradientDerivative_sq
    ((contDiff_gradient_of_contDiff_two hφ).differentiable (by norm_num)) A U x
    (hessianMatrix_isSymm hφ x) hU

/-- The contracted trace is genuinely integrable, not a default-valued
Bochner integral. -/
theorem integrable_transported_hessian_contraction {φ : Space n → ℝ}
    [IsFiniteMeasure (potentialMeasure φ)] (hφ : ContDiff ℝ 2 φ)
    {B : ℝ} (hB : ∀ x, ‖fderiv ℝ (gradient φ) x‖ ≤ B)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    Integrable (fun x =>
      (A.transpose * A * hessianMatrix φ x * (A.transpose * A) * hessianMatrix φ x).trace)
      (potentialMeasure φ) := by
  have hi := integrable_finsetSum Finset.univ fun i _ =>
    integrable_transportedGradientDerivative_sq hφ hB A
      (WithLp.toLp 2 ((1 : Matrix (Fin n) (Fin n) ℝ) i))
  apply hi.congr
  exact Eventually.of_forall fun x => sum_transportedGradientDerivative_sq
    ((contDiff_gradient_of_contDiff_two hφ).differentiable (by norm_num)) A 1 x
    (hessianMatrix_isSymm hφ x) (by simp)

end MomentMap

/-- The quadratic variance conclusion in the exact transported trace form.
Moment-map representation and diffusion-range density remain explicit. -/
theorem quadratic_variance_le_transported_hessian_contraction {n : ℕ} {φ V : Space n → ℝ}
    [IsFiniteMeasure (potentialMeasure φ)] [IsProbabilityMeasure (potentialMeasure V)]
    (hφ : ContDiff ℝ 2 φ) (hV : ContDiff ℝ 2 V) (hconv : ConvexOn ℝ univ V)
    (A U : Matrix (Fin n) (Fin n) ℝ) (hU : U.IsSymm) (hUorth : U.transpose * U = 1)
    (hpush : MomentMap.linearGradientPushforward φ A = potentialMeasure V)
    {B : ℝ} (hB : ∀ x, ‖fderiv ℝ (gradient φ) x‖ ≤ B)
    (hq : MemLp (matrixQuadratic U) 2 (potentialMeasure V))
    (hdense : DiffusionRangeDense V) :
    ProbabilityTheory.variance (matrixQuadratic U) (potentialMeasure V) ≤
      4 * ∫ x, (A.transpose * A * MomentMap.hessianMatrix φ x *
        (A.transpose * A) * MomentMap.hessianMatrix φ x).trace ∂potentialMeasure φ := by
  have hh := quadratic_variance_le_linear_momentMap_energy
    (hφ.differentiable (by norm_num)) (MomentMap.contDiff_gradient_of_contDiff_two hφ)
    hV hconv A hpush hB U hU hq hdense
  rwa [MomentMap.sum_integral_transportedGradientDerivative_sq hφ hB A U hUorth] at hh

end KLS
end

#print axioms KLS.MomentMap.hessianMatrix_isSymm
#print axioms KLS.MomentMap.sum_integral_transportedGradientDerivative_sq
#print axioms KLS.MomentMap.integrable_transported_hessian_contraction
#print axioms KLS.quadratic_variance_le_transported_hessian_contraction

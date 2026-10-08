import KLS.RawMomentMapStein
import KLS.AffineMomentMapContraction

open MeasureTheory ProbabilityTheory InnerProductSpace Matrix Set Filter
open scoped BigOperators ContDiff NNReal
noncomputable section
namespace KLS
namespace MomentMap
variable {n : ℕ}

theorem rawTransportedHessianDerivative_eq_matrixAction
    (φ : Space n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (x w : Space n) :
    rawTransportedHessianDerivative φ A x w =
      matrixAction (A * coordinateHessian φ x * A.transpose) w := by
  simp only [rawTransportedHessianDerivative, matrixAction_mul_apply]

/-- Finite sums and integrals are exchanged only after the actual raw
 Hessian energies have been proved integrable. Symmetry is derived a.e. -/
theorem sum_integral_rawTransportedHessianDerivative_sq_C11
    {φ : Space n → ℝ} {G : ℝ≥0} [IsFiniteMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 1 φ) (hG : LipschitzWith G (gradient φ))
    (A U : Matrix (Fin n) (Fin n) ℝ) (hU : U.transpose * U = 1) :
    (∑ i : Fin n, ∫ x, ‖rawTransportedHessianDerivative φ A x (WithLp.toLp 2 (U i))‖ ^ 2
      ∂potentialMeasure φ) =
      ∫ x, (A.transpose * A * coordinateHessian φ x *
        (A.transpose * A) * coordinateHessian φ x).trace ∂potentialMeasure φ := by
  rw [← integral_finsetSum Finset.univ (fun i _ =>
    (memLp_rawTransportedHessianDerivative hG A (WithLp.toLp 2 (U i)) 2).norm.integrable_sq)]
  have hsym := actual_hessian_ae_symmetric_of_locallyLipschitz_gradient
    hφ.locallyLipschitz hG.locallyLipschitz
  have hac : potentialMeasure φ ≪ volume := withDensity_absolutelyContinuous _ _
  apply integral_congr_ae
  filter_upwards [hsym.filter_mono hac.ae_le] with x hx
  simp_rw [rawTransportedHessianDerivative_eq_matrixAction]
  exact transported_stein_energy_contraction A (coordinateHessian φ x) U hx hU

theorem integrable_raw_transported_hessian_contraction_C11
    {φ : Space n → ℝ} {G : ℝ≥0} [IsFiniteMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 1 φ) (hG : LipschitzWith G (gradient φ))
    (A : Matrix (Fin n) (Fin n) ℝ) :
    Integrable (fun x => (A.transpose * A * coordinateHessian φ x *
      (A.transpose * A) * coordinateHessian φ x).trace) (potentialMeasure φ) := by
  have hi := integrable_finsetSum Finset.univ fun i _ =>
    (memLp_rawTransportedHessianDerivative (μ := potentialMeasure φ) hG A
      (WithLp.toLp 2 ((1 : Matrix (Fin n) (Fin n) ℝ) i)) 2).norm.integrable_sq
  have hsym := actual_hessian_ae_symmetric_of_locallyLipschitz_gradient
    hφ.locallyLipschitz hG.locallyLipschitz
  have hac : potentialMeasure φ ≪ volume := withDensity_absolutelyContinuous _ _
  apply hi.congr
  filter_upwards [hsym.filter_mono hac.ae_le] with x hx
  simp_rw [rawTransportedHessianDerivative_eq_matrixAction]
  exact transported_stein_energy_contraction A (coordinateHessian φ x) 1 hx (by simp)

end MomentMap
end KLS
end

import KLS.QuadraticCovarianceOperator
import KLS.IsotropicSecondTaylor
import KLS.FaithfulFullTaylorCriterion
import KLS.QuadraticDamping

open MeasureTheory ProbabilityTheory InnerProductSpace Matrix Set
open scoped BigOperators ContDiff ENNReal
noncomputable section
namespace KLS
variable {n : ℕ} {V : Space n → ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure V)]
  (hV : ContDiff ℝ 2 V) (hκ : 0 < κ)
  (hstrong : StrongConvexOn univ κ V)
  (hiso : IsIsotropic (potentialMeasure V))

include hV hκ hstrong hiso

/-- The literal degree-two tensor is exactly one half of the actual
symmetric covariance matrix, with all coordinate-product integrability
proved from the actual strongly convex density. -/
theorem exponentialTiltCoordinateTaylor_two_eq_covariance
    (f : Lp ℝ 2 (potentialMeasure V)) (a : Fin 2 → Fin n) :
    exponentialTiltCoordinateTaylor V f 2 a =
      quadraticCovarianceMatrix (potentialMeasure V) f (a 0) (a 1) / 2 := by
  have hLC := measureLogConcave_potentialMeasure hV.continuous.measurable
    (convexOn_of_strongConvexOn_nonneg hκ.le hstrong)
  rw [exponentialTiltCoordinateTaylor_two_of_isotropic hV hκ
    (coordinateHessian_lower_of_strongConvexOn hV hstrong) hiso (Lp.memLp f),
    quadraticCovarianceMatrix, covariance_eq_sub (Lp.memLp f)
      (hLC.memLp_two_coordinate_mul (a 0) (a 1)), hiso.integral_coordinate_mul]
  rfl

/-- Both ordered off-diagonal coordinates are included in the genuine
Frobenius norm; the Taylor factorial contributes exactly a factor four. -/
theorem sum_exponentialTiltCoordinateTaylor_two_sq_eq_frobenius
    (f : Lp ℝ 2 (potentialMeasure V)) :
    (∑ a : Fin 2 → Fin n, exponentialTiltCoordinateTaylor V f 2 a ^ 2) =
      matrixFrobeniusSq (quadraticCovarianceMatrix (potentialMeasure V) f) / 4 := by
  simp_rw [exponentialTiltCoordinateTaylor_two_eq_covariance hV hκ hstrong hiso f]
  have he : (∑ a : Fin 2 → Fin n,
      (quadraticCovarianceMatrix (potentialMeasure V) f (a 0) (a 1) / 2) ^ 2) =
      ∑ p : Fin n × Fin n, (quadraticCovarianceMatrix (potentialMeasure V) f p.1 p.2 / 2) ^ 2 :=
    Fintype.sum_equiv (finTwoArrowEquiv (Fin n)) _ _ (fun _ => rfl)
  rw [he, Fintype.sum_prod_type]
  simp only [div_pow, show (2 : ℝ) ^ 2 = 4 by norm_num,
    ← Finset.sum_div, matrixFrobeniusSq]

/-- Quadratic-eight gives the exact degree-two operator constant two on
all genuine L2 observables. The displayed quadratic input remains explicit. -/
theorem QuadraticVarianceEight.secondTaylor_norm_bound
    (hQ : QuadraticVarianceEight (potentialMeasure V))
    (f : Lp ℝ 2 (potentialMeasure V)) :
    (∑ a : Fin 2 → Fin n, exponentialTiltCoordinateTaylor V f 2 a ^ 2) ≤ 2 * ‖f‖ ^ 2 := by
  rw [sum_exponentialTiltCoordinateTaylor_two_sq_eq_frobenius hV hκ hstrong hiso]
  have hh := hQ.quadraticCovariance_frobeniusSq_le_norm f
  linarith

/-- Conversely the exact degree-two bound recovers quadratic-eight through
a centered quadratic test and genuine symmetric Frobenius duality. -/
theorem quadraticVarianceEight_of_secondTaylor_norm_bound
    (hbound : ∀ f : Lp ℝ 2 (potentialMeasure V),
      (∑ a : Fin 2 → Fin n, exponentialTiltCoordinateTaylor V f 2 a ^ 2) ≤ 2 * ‖f‖ ^ 2) :
    QuadraticVarianceEight (potentialMeasure V) := by
  have hLC := measureLogConcave_potentialMeasure hV.continuous.measurable
    (convexOn_of_strongConvexOn_nonneg hκ.le hstrong)
  apply quadraticVarianceEight_of_quadraticCovariance_norm_bound hLC.memLp_two_coordinate_mul
  intro f
  have hh := hbound f
  rw [sum_exponentialTiltCoordinateTaylor_two_sq_eq_frobenius hV hκ hstrong hiso] at hh
  linarith

/-- An exact equivalence on the actual regular isotropic class. Neither side
is asserted globally; the sharp constants eight and two include the true
Taylor factorial and the full symmetric Frobenius norm. -/
theorem quadraticVarianceEight_iff_secondTaylor_norm_bound :
    QuadraticVarianceEight (potentialMeasure V) ↔
      ∀ f : Lp ℝ 2 (potentialMeasure V),
        (∑ a : Fin 2 → Fin n, exponentialTiltCoordinateTaylor V f 2 a ^ 2) ≤ 2 * ‖f‖ ^ 2 := by
  exact ⟨fun hQ => hQ.secondTaylor_norm_bound hV hκ hstrong hiso,
    quadraticVarianceEight_of_secondTaylor_norm_bound hV hκ hstrong hiso⟩

end KLS
end

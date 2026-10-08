import KLS.AdaptiveCoordinateCovarianceBounds
import KLS.AdaptiveCovarianceGenerator
import LevyStochCalc.Brownian.CoordDerivative

/-! The true coordinate generator agrees with the adaptive covariance generator. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS.AdaptiveLocalization
open LevyStochCalc
variable {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

theorem coordinateCovarianceGradient_apply (hμ : IsCompact μ.support)
    (i j : Fin n) (z v : Fin (n+n*n) → ℝ) :
    coordinateCovarianceGradient μ i j z v =
      covarianceGradient μ i j (decodeState z) (decodeState v) := by
  rw [coordinateCovarianceGradient_apply_eq_cumulant hμ, covarianceGradient_apply_eq_cumulant hμ]
  rfl

theorem coordinateCovarianceHessian_apply (hμ : IsCompact μ.support)
    (i j : Fin n) (z u v : Fin (n+n*n) → ℝ) :
    coordinateCovarianceHessian μ i j z u v =
      covarianceHessian μ i j (decodeState z) (decodeState u) (decodeState v) := by
  rw [coordinateCovarianceHessian_apply_eq_cumulant hμ, covarianceHessian_apply_eq_cumulant hμ]
  rfl

theorem coordinateCovariance_generator (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (i j : Fin n) (z : Fin (n+n*n) → ℝ) :
    coordinateCovarianceGradient μ i j z (coordinateDrift μ z) +
      1/2 * ∑ k : Fin n, coordinateCovarianceHessian μ i j z
        (coordinateDiffusion μ k z) (coordinateDiffusion μ k z) =
      -coordinateCovariance μ i j z := by
  simp_rw [coordinateCovarianceGradient_apply hμ, coordinateCovarianceHessian_apply hμ,
    coordinateDrift, coordinateDiffusion, decode_encodeState]
  exact covarianceGenerator_eq_neg_covariance hμ hfull (decodeState z) i j

theorem coordinateCovariance_generator_sum (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (i j : Fin n) (z : Fin (n+n*n) → ℝ) :
    (∑ a : Fin (n+n*n), coordDeriv (coordinateCovarianceGradient μ i j) a z * coordinateDrift μ z a) +
      1/2 * ∑ a : Fin (n+n*n), ∑ b : Fin (n+n*n),
        coordDeriv₂ (coordinateCovarianceHessian μ i j) a b z *
          ∑ k : Fin n, coordinateDiffusion μ k z a * coordinateDiffusion μ k z b =
      -coordinateCovariance μ i j z := by
  have h := coordinateCovariance_generator hμ hfull i j z
  rw [apply_eq_sum_coordDeriv] at h
  simp_rw [apply₂_eq_sum_coordDeriv₂] at h
  have hd : (∑ a : Fin (n+n*n), coordDeriv (coordinateCovarianceGradient μ i j) a z * coordinateDrift μ z a) =
      ∑ a : Fin (n+n*n), coordinateDrift μ z a * coordDeriv (coordinateCovarianceGradient μ i j) a z := by
    apply Finset.sum_congr rfl
    intro a _
    ring
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
#print axioms KLS.AdaptiveLocalization.coordinateCovariance_generator_sum

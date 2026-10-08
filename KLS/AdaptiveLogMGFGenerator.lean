import KLS.AdaptiveLogMGFDerivatives

/-! Actual log-MGF noise and the exact negative half-square generator. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS.AdaptiveLocalization
open LevyStochCalc KLS.LocalDiffusion
variable {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

def logMGFNoiseCoefficient (μ : Measure (Space n)) (w : Space n) (k : Fin n)
    (z : Fin (n+n*n) → ℝ) : ℝ := coordinateLogMGFGradient μ w z (coordinateDiffusion μ k z)

def logMGFDrift (μ : Measure (Space n)) (w : Space n) (z : Fin (n+n*n) → ℝ) : ℝ :=
  -(1/2) * ∑ k : Fin n, (logMGFNoiseCoefficient μ w k z)^2

theorem logMGFNoiseCoefficient_eq_ratio (hμ : IsCompact μ.support) (w : Space n)
    (k : Fin n) (z : Fin (n+n*n) → ℝ) : logMGFNoiseCoefficient μ w k z =
      averageNoiseCoefficient μ (exponentialObservable w) k z /
        coordinateAverage μ (exponentialObservable w) z :=
  coordinateLogMGFGradient_apply hμ w z _

/-- The actual log-MGF generator, with no stochastic equation assumed. -/
theorem coordinateLogMGF_generator (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (w : Space n) (z : Fin (n+n*n) → ℝ) :
    coordinateLogMGFGradient μ w z (coordinateDrift μ z) +
      1/2 * ∑ k : Fin n, coordinateLogMGFHessian μ w z
        (coordinateDiffusion μ k z) (coordinateDiffusion μ k z) = logMGFDrift μ w z := by
  have ha := coordinateAverage_generator_zero hμ hfull (integrable_exponentialObservable hμ w) z
  have hh := congrArg (fun a : ℝ => a / coordinateAverage μ (exponentialObservable w) z) ha
  rw [add_div, mul_div_assoc, zero_div] at hh
  rw [coordinateLogMGFGradient_apply hμ w]
  simp_rw [coordinateLogMGFHessian_apply_self hμ w]
  rw [Finset.sum_sub_distrib, ← Finset.sum_div]
  unfold logMGFDrift
  simp_rw [logMGFNoiseCoefficient_eq_ratio hμ w]
  change _ = -(1/2) * ∑ k : Fin n,
    (coordinateAverageGradient μ (exponentialObservable w) z (coordinateDiffusion μ k z) /
      coordinateAverage μ (exponentialObservable w) z)^2
  linarith

/-- Coordinate form consumed by the actual local Itô theorem. -/
theorem observableGenerator_coordinateLogMGF (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (w : Space n) (z : Fin (n+n*n) → ℝ) :
    observableGenerator (coordinateDrift μ) (coordinateDiffusion μ)
      (coordinateLogMGFGradient μ w) (coordinateLogMGFHessian μ w) z = logMGFDrift μ w z := by
  have h := coordinateLogMGF_generator hμ hfull w z
  rw [apply_eq_sum_coordDeriv] at h
  simp_rw [apply₂_eq_sum_coordDeriv₂] at h
  unfold observableGenerator
  have hd : (∑ a : Fin (n+n*n), coordDeriv (coordinateLogMGFGradient μ w) a z * coordinateDrift μ z a) =
      ∑ a : Fin (n+n*n), coordinateDrift μ z a * coordDeriv (coordinateLogMGFGradient μ w) a z :=
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
#print axioms KLS.AdaptiveLocalization.coordinateLogMGF_generator
#print axioms KLS.AdaptiveLocalization.observableGenerator_coordinateLogMGF

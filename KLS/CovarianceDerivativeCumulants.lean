import KLS.LocalizationCovarianceDerivative
import LevyStochCalc.Brownian.CoordDerivative

/-! Identification of the actual covariance Fréchet derivatives with the
actual centered third and fourth cumulants of the normalized law. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
noncomputable section
namespace KLS.StandardLocalization
open LevyStochCalc
variable {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

theorem covarianceGradient_apply_eq_cumulant (hμ : IsCompact μ.support)
    (i j : Fin n) (z v : Fin (n + 1) → ℝ) :
    covarianceGradient μ i j z v =
      tiltThirdCumulant μ (exponent (z 0) (Fin.tail z))
        (fun x => x i) (fun x => x j) (augmentedScore v) := by
  have hp : HasDerivAt (fun s : ℝ => z + s • v) v 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z using 1 <;> simp
  have hc := (hasFDerivAt_augmentedCovariance hμ i j z).comp_hasDerivAt_of_eq 0 hp (by simp)
  have hd := hasDerivAt_augmentedCovariance_line hμ i j z v 0
  have hc' : HasDerivAt (fun s : ℝ => augmentedCovariance μ i j (z + s • v))
      (covarianceGradient μ i j z v) 0 := by
    convert hc using 1
    funext s
    rfl
  exact hc'.unique (by simpa only [zero_smul, add_zero] using hd)

theorem covarianceHessian_apply_eq_cumulant (hμ : IsCompact μ.support)
    (i j : Fin n) (z u v : Fin (n + 1) → ℝ) :
    covarianceHessian μ i j z u v =
      tiltFourthCumulant μ (exponent (z 0) (Fin.tail z))
        (fun x => x i) (fun x => x j) (augmentedScore v) (augmentedScore u) := by
  have hp : HasDerivAt (fun s : ℝ => z + s • u) u 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add z using 1 <;> simp
  have hc := (hasFDerivAt_covarianceGradient hμ i j z).comp_hasDerivAt_of_eq 0 hp (by simp)
  have he := hc.clm_apply (hasDerivAt_const (0 : ℝ) v)
  have he' : HasDerivAt (fun s : ℝ => covarianceGradient μ i j (z + s • u) v)
      (covarianceHessian μ i j z u v) 0 := by
    convert he using 1 <;> simp
  have hd := hasDerivAt_tiltThirdCumulant hμ (continuous_exponent_state (z 0) (Fin.tail z))
    (f := fun x => x i) (g := fun x => x j) (by fun_prop) (by fun_prop)
    (continuous_augmentedScore v) (continuous_augmentedScore u) 0
  have hd' : HasDerivAt (fun s : ℝ => covarianceGradient μ i j (z + s • u) v)
      (tiltFourthCumulant μ (exponent (z 0) (Fin.tail z))
        (fun x => x i) (fun x => x j) (augmentedScore v) (augmentedScore u)) 0 := by
    simp_rw [covarianceGradient_apply_eq_cumulant hμ]
    simpa only [augmented_exponent_line, zero_mul, add_zero] using hd
  exact he'.unique hd'

theorem augmentedScore_single (p : Fin (n + 1)) :
    augmentedScore (Pi.single p 1) = fun x : Space n => localizationFeature x p := by
  funext x
  simp [augmentedScore, score, Pi.single_apply]

theorem covariance_time_derivative (hμ : IsCompact μ.support)
    (i j : Fin n) (z : Fin (n + 1) → ℝ) :
    coordDeriv (covarianceGradient μ i j) 0 z =
      tiltThirdCumulant μ (exponent (z 0) (Fin.tail z))
        (fun x => x i) (fun x => x j) (fun x => -‖x‖ ^ 2 / 2) := by
  rw [coordDeriv, covarianceGradient_apply_eq_cumulant hμ, augmentedScore_single]
  rfl

theorem covariance_space_derivative (hμ : IsCompact μ.support)
    (i j k : Fin n) (z : Fin (n + 1) → ℝ) :
    coordDeriv (covarianceGradient μ i j) k.succ z =
      tiltThirdCumulant μ (exponent (z 0) (Fin.tail z))
        (fun x => x i) (fun x => x j) (fun x => x k) := by
  rw [coordDeriv, covarianceGradient_apply_eq_cumulant hμ, augmentedScore_single]
  rfl

theorem covariance_space_second_derivative (hμ : IsCompact μ.support)
    (i j k l : Fin n) (z : Fin (n + 1) → ℝ) :
    coordDeriv₂ (covarianceHessian μ i j) k.succ l.succ z =
      tiltFourthCumulant μ (exponent (z 0) (Fin.tail z))
        (fun x => x i) (fun x => x j) (fun x => x l) (fun x => x k) := by
  rw [coordDeriv₂, covarianceHessian_apply_eq_cumulant hμ,
    augmentedScore_single, augmentedScore_single]
  rfl

end KLS.StandardLocalization
end
#print axioms KLS.StandardLocalization.covarianceGradient_apply_eq_cumulant
#print axioms KLS.StandardLocalization.covarianceHessian_apply_eq_cumulant

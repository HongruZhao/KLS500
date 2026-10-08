import KLS.AdaptiveCoefficients
import KLS.CovarianceCumulantPDE

/-! Actual Frechet derivatives of the general matrix-quadratic covariance. -/
open MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS.AdaptiveLocalization
variable {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

theorem exponent_line (p v : Parameter n) (s : ℝ) :
    exponent (p + s • v).1 (p + s • v).2 =
      fun x => exponent p.1 p.2 x + s * exponent v.1 v.2 x := by
  funext x
  change (∑ i, (p.1 i + s * v.1 i) * x i) -
      (∑ i, ∑ j, (p.2 i j + s * v.2 i j) * x i * x j) / 2 =
    ((∑ i, p.1 i * x i) - (∑ i, ∑ j, p.2 i j * x i * x j) / 2) +
      s * ((∑ i, v.1 i * x i) - (∑ i, ∑ j, v.2 i j * x i * x j) / 2)
  simp_rw [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  ring

def covarianceGradient (μ : Measure (Space n)) (i j : Fin n) :
    Parameter n → Parameter n →L[ℝ] ℝ :=
  fderiv ℝ (fun p : Parameter n => covariance μ p.1 p.2 i j)

def covarianceHessian (μ : Measure (Space n)) (i j : Fin n) :
    Parameter n → Parameter n →L[ℝ] Parameter n →L[ℝ] ℝ :=
  fderiv ℝ (covarianceGradient μ i j)

theorem hasFDerivAt_covariance (hμ : IsCompact μ.support) (i j : Fin n) (p : Parameter n) :
    HasFDerivAt (fun p : Parameter n => covariance μ p.1 p.2 i j)
      (covarianceGradient μ i j p) p :=
  ((contDiff_covariance hμ i j).differentiable (by simp) p).hasFDerivAt

theorem contDiff_covarianceGradient (hμ : IsCompact μ.support) (i j : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (covarianceGradient μ i j) :=
  (contDiff_covariance hμ i j).fderiv_right (m := (⊤ : ℕ∞)) (by simp)

theorem hasFDerivAt_covarianceGradient (hμ : IsCompact μ.support) (i j : Fin n) (p : Parameter n) :
    HasFDerivAt (covarianceGradient μ i j) (covarianceHessian μ i j p) p :=
  ((contDiff_covarianceGradient hμ i j).differentiable (by simp) p).hasFDerivAt

theorem covarianceGradient_apply_eq_cumulant (hμ : IsCompact μ.support)
    (i j : Fin n) (p v : Parameter n) :
    covarianceGradient μ i j p v = tiltThirdCumulant μ (exponent p.1 p.2)
      (fun x => x i) (fun x => x j) (exponent v.1 v.2) := by
  have hp : HasDerivAt (fun s : ℝ => p + s • v) v 0 := by
    convert! ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add p using 1 <;>
      simp only [Pi.add_apply, id_eq, one_smul, zero_add]
  have hc := (hasFDerivAt_covariance hμ i j p).comp_hasDerivAt_of_eq 0 hp (by simp)
  have hc' : HasDerivAt (fun s : ℝ => covariance μ (p + s • v).1 (p + s • v).2 i j)
      (covarianceGradient μ i j p v) 0 := by
    convert hc using 1
    funext s
    rfl
  have hd := hasDerivAt_tilted_covariance hμ (continuous_exponent p.1 p.2)
    (f := fun x => x i) (g := fun x => x j)
    (by fun_prop) (by fun_prop) (continuous_exponent v.1 v.2) (0 : ℝ)
  apply hc'.unique
  change HasDerivAt (fun s => ProbabilityTheory.covariance (fun x : Space n => x i)
    (fun x : Space n => x j) (μ.tilted (exponent (p + s • v).1 (p + s • v).2))) _ 0
  simp_rw [exponent_line]
  simpa only [zero_mul, add_zero] using hd

theorem covarianceHessian_apply_eq_cumulant (hμ : IsCompact μ.support)
    (i j : Fin n) (p u v : Parameter n) :
    covarianceHessian μ i j p u v = tiltFourthCumulant μ (exponent p.1 p.2)
      (fun x => x i) (fun x => x j) (exponent v.1 v.2) (exponent u.1 u.2) := by
  have hp : HasDerivAt (fun s : ℝ => p + s • u) u 0 := by
    convert! ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add p using 1 <;>
      simp only [Pi.add_apply, id_eq, one_smul, zero_add]
  have hc := (hasFDerivAt_covarianceGradient hμ i j p).comp_hasDerivAt_of_eq 0 hp (by simp)
  have he := hc.clm_apply (hasDerivAt_const (0 : ℝ) v)
  have he' : HasDerivAt (fun s : ℝ => covarianceGradient μ i j (p + s • u) v)
      (covarianceHessian μ i j p u v) 0 := by
    convert he using 1 <;> simp
  have hd := hasDerivAt_tiltThirdCumulant hμ (continuous_exponent p.1 p.2)
    (f := fun x => x i) (g := fun x => x j) (by fun_prop) (by fun_prop)
    (continuous_exponent v.1 v.2) (continuous_exponent u.1 u.2) 0
  have hd' : HasDerivAt (fun s : ℝ => covarianceGradient μ i j (p + s • u) v)
      (tiltFourthCumulant μ (exponent p.1 p.2)
        (fun x => x i) (fun x => x j) (exponent v.1 v.2) (exponent u.1 u.2)) 0 := by
    simp_rw [covarianceGradient_apply_eq_cumulant hμ]
    simpa only [exponent_line, zero_mul, add_zero] using hd
  exact he'.unique hd'

end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.covarianceGradient_apply_eq_cumulant
#print axioms KLS.AdaptiveLocalization.covarianceHessian_apply_eq_cumulant

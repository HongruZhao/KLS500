import KLS.TiltCumulants
import KLS.TiltMoments
import KLS.TiltCovariancePositive
import OptVarianceGlobal

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff
noncomputable section
namespace KLS.ConstantReduction
variable {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

theorem contDiff_tiltVariance (hμ : IsCompact μ.support)
    {q f : Space n → ℝ} (hq : Continuous q) (hf : Continuous f) :
    ContDiff ℝ 2 (fun t : ℝ => ProbabilityTheory.variance f (μ.tilted (fun x => q x + t * f x))) := by
  have hd (a : Space n → ℝ) (ha : Continuous a) :=
    contDiff_tiltAverage hμ hq hf (integrable_of_continuous_compact_support_measure hμ ha)
  have heq (t : ℝ) : ProbabilityTheory.variance f (μ.tilted (fun x => q x + t * f x)) =
      tiltAverage μ (fun x => q x + t * f x) (fun x => f x * f x) -
        tiltAverage μ (fun x => q x + t * f x) f * tiltAverage μ (fun x => q x + t * f x) f := by
    rw [← covariance_self hf.measurable.aemeasurable]
    have := tilted_isProbability_of_compact_support hμ (q := fun x => q x + t * f x) (by fun_prop)
    exact covariance_eq_sub (memLp_two_continuous_tilted hμ (by fun_prop) hf)
      (memLp_two_continuous_tilted hμ (by fun_prop) hf)
  simp_rw [heq]
  exact ((hd _ (hf.mul hf)).sub ((hd _ hf).mul (hd _ hf))).of_le (by simp)

theorem deriv_tiltVariance (hμ : IsCompact μ.support)
    {q f : Space n → ℝ} (hq : Continuous q) (hf : Continuous f) (t : ℝ) :
    deriv (fun u : ℝ => ProbabilityTheory.variance f (μ.tilted (fun x => q x + u * f x))) t =
      tiltThirdCumulant μ (fun x => q x + t * f x) f f f := by
  have hd := hasDerivAt_tilted_covariance hμ hq hf hf hf t
  simp_rw [covariance_self hf.measurable.aemeasurable] at hd
  exact hd.deriv

theorem deriv_deriv_tiltVariance (hμ : IsCompact μ.support)
    {q f : Space n → ℝ} (hq : Continuous q) (hf : Continuous f) (t : ℝ) :
    deriv (deriv (fun u : ℝ => ProbabilityTheory.variance f (μ.tilted (fun x => q x + u * f x)))) t =
      tiltFourthCumulant μ (fun x => q x + t * f x) f f f f := by
  have heq := funext (deriv_tiltVariance hμ hq hf)
  rw [heq]
  exact (hasDerivAt_tiltThirdCumulant hμ hq hf hf hf hf t).deriv

theorem tiltFourthCumulant_same_eq_centered_square_variance
    (hμ : IsCompact μ.support) {q f : Space n → ℝ} (hq : Continuous q) (hf : Continuous f) :
    tiltFourthCumulant μ q f f f f =
      ProbabilityTheory.variance (fun x => (f x - tiltAverage μ q f)^2) (μ.tilted q) -
        2 * (ProbabilityTheory.variance f (μ.tilted q))^2 := by
  have := tilted_isProbability_of_compact_support hμ hq
  have h2 := memLp_two_continuous_tilted hμ hq (show Continuous (fun x => (f x - tiltAverage μ q f)^2) by fun_prop)
  rw [variance_eq_sub h2]
  have hi : (∫ x, (f x - tiltAverage μ q f)^2 ∂μ.tilted q) = ProbabilityTheory.variance f (μ.tilted q) := by
    exact (variance_eq_integral hf.measurable.aemeasurable).symm
  rw [hi]
  simp only [tiltFourthCumulant, covariance_self hf.measurable.aemeasurable, tiltAverage]
  have heq : (fun x => (f x - ∫ y, f y ∂μ.tilted q) * (f x - ∫ y, f y ∂μ.tilted q) *
      (f x - ∫ y, f y ∂μ.tilted q) * (f x - ∫ y, f y ∂μ.tilted q)) =
    (fun x => ((f x - ∫ y, f y ∂μ.tilted q)^2)^2) := by funext x; ring
  rw [heq]
  simp only [Pi.pow_apply]
  ring

theorem tiltThirdCumulant_same_sq_le_of_centered_square_variance
    (hμ : IsCompact μ.support) {q f : Space n → ℝ} (hq : Continuous q) (hf : Continuous f)
    (hpos : ∀ t : ℝ, 0 < ProbabilityTheory.variance f (μ.tilted (fun x => q x + t * f x)))
    (hQ : ∀ t : ℝ, ProbabilityTheory.variance (fun x => (f x - tiltAverage μ (fun x => q x + t * f x) f)^2)
      (μ.tilted (fun x => q x + t * f x)) ≤ 8 * (ProbabilityTheory.variance f (μ.tilted (fun x => q x + t * f x)))^2)
    (t : ℝ) :
    (tiltThirdCumulant μ (fun x => q x + t * f x) f f f)^2 ≤
      4 * (ProbabilityTheory.variance f (μ.tilted (fun x => q x + t * f x)))^3 := by
  have hsecond (u : ℝ) :
      deriv (deriv (fun z : ℝ => ProbabilityTheory.variance f (μ.tilted (fun x => q x + z * f x)))) u ≤
        6 * (ProbabilityTheory.variance f (μ.tilted (fun x => q x + u * f x)))^2 := by
    rw [deriv_deriv_tiltVariance hμ hq hf,
      tiltFourthCumulant_same_eq_centered_square_variance hμ (by fun_prop) hf]
    linarith [hQ u]
  have h := varianceODE_deriv_sq_le (contDiff_tiltVariance hμ hq hf) hpos hsecond t
  rwa [deriv_tiltVariance hμ hq hf] at h

end KLS.ConstantReduction
end

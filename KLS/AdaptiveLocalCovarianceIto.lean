import KLS.AdaptiveCovarianceNoise

/-! The covariance of the actual adaptive ball process satisfies its claimed SDE. -/
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix.Norms.Elementwise
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS.AdaptiveLocalization
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
open LevyStochCalc.Brownian.Ito KLS.LocalDiffusion KLSLevyProbe
universe u
variable {n : ℕ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {μ : Measure (Space n)} [IsProbabilityMeasure μ]
  {W : MultidimBrownianMotion P n} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ} {R : ℝ}

namespace BallProcess
variable (D : BallProcess μ W ℱ hW R)

def covariancePath (t : ℝ) (ω : Ω) : Matrix (Fin n) (Fin n) ℝ :=
  covariance μ (D.parameterPath t ω).1 (D.parameterPath t ω).2

/-- For the genuinely constructed adaptive process, the covariance drift is
exactly minus covariance and the noise is the stopped third-cumulant coefficient.
There is no premise asserting a covariance differential or an abstract SDE. -/
theorem covariance_equation (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[ℱ 0] A)
    (i j : Fin n) {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, (T : WithTop ℝ) ≤ D.exit ω →
      D.covariancePath T ω i j - covariance μ 0 0 i j =
        -(∫ t in Icc (0 : ℝ) T, D.covariancePath t ω i j ∂volume) +
          ∑ k : Fin n, D.covarianceNoiseIntegral hμ i j k T ω := by
  have hc := (contDiff_coordinateCovarianceGradient hμ i j).continuous
  have hc₂ : Continuous (coordinateCovarianceHessian μ i j) :=
    ((contDiff_coordinateCovarianceGradient hμ i j).fderiv_right (m := (⊤ : ℕ∞)) (by simp)).continuous
  have hi := D.itoFormula_original_generator hℱ0 hnull
    ((contDiff_coordinateCovariance hμ i j).of_le (by simp))
    (hasFDerivAt_coordinateCovariance hμ i j) (hasFDerivAt_coordinateCovarianceGradient hμ i j)
    hc hc₂ (covarianceGradientBound_nonneg hμ) (covarianceGradient_norm_le hμ i j) hT
  have hg : observableGenerator (coordinateDrift μ) (coordinateDiffusion μ)
      (coordinateCovarianceGradient μ i j) (coordinateCovarianceHessian μ i j) =
      fun z => -coordinateCovariance μ i j z := by
    funext z
    exact coordinateCovariance_generator_sum hμ hfull i j z
  have hn : ∀ᵐ ω ∂P, ∀ k : Fin n,
      D.covarianceNoiseIntegral hμ i j k T ω =
        ∑ a : Fin (n+n*n), D.observableNoiseIntegral (coordinateCovarianceGradient μ i j) hc
          (covarianceGradientBound_nonneg hμ) (covarianceGradient_norm_le hμ i j) a k T ω :=
    ae_all_iff.mpr fun k => D.covarianceNoiseIntegral_eq_sum hμ i j k hT
  filter_upwards [hi, D.initial_Y, hn] with ω hI h0 hnoise hle
  have h := hI hle
  rw [hg, integral_neg] at h
  have hs : (∑ a : Fin (n+n*n), ∑ k : Fin n,
      D.observableNoiseIntegral (coordinateCovarianceGradient μ i j) hc
        (covarianceGradientBound_nonneg hμ) (covarianceGradient_norm_le hμ i j) a k T ω) =
      ∑ k : Fin n, D.covarianceNoiseIntegral hμ i j k T ω := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => (hnoise k).symm
  rw [hs, h0] at h
  simpa only [coordinateCovariance, covariancePath, parameterPath, decodeState_zero, Prod.fst_zero, Prod.snd_zero] using h

end BallProcess
end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.BallProcess.covariance_equation

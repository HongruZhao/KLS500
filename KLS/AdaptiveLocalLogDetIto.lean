import KLS.AdaptiveLogDetGenerator
import KLS.LocalSmoothObservableIto

/-! Actual Brownian integrals and local Itô equation for covariance log determinant. -/
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix.Norms.Elementwise
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS.AdaptiveLocalization
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
open LevyStochCalc.Brownian.Ito KLS.LocalDiffusion KLSLevyProbe
universe u
variable {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

theorem logDetNoiseCoefficient_eq_sum (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (k : Fin n) (z : Fin (n+n*n) → ℝ) :
    logDetNoiseCoefficient μ k z = ∑ a : Fin (n+n*n),
      coordDeriv (coordinateLogDetGradient μ) a z * coordinateDiffusion μ k z a := by
  rw [show logDetNoiseCoefficient μ k z = coordinateLogDetGradient μ z (coordinateDiffusion μ k z)
    from (coordinateLogDet_noise hμ hfull z k).symm, apply_eq_sum_coordDeriv]
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {W : MultidimBrownianMotion P n} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ} {R : ℝ}
namespace BallProcess
variable (D : BallProcess μ W ℱ hW R)

def logDetNoise (k : Fin n) : Ω → ℝ → ℝ :=
  Probability.stopped D.exit (fun ω t => logDetNoiseCoefficient μ k (D.pair.Y t ω))

theorem logDetNoise_eq_sum (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (k : Fin n) : D.logDetNoise k =
    fun ω t => ∑ a : Fin (n+n*n), D.observableNoise (coordinateLogDetGradient μ) a k ω t := by
  funext ω t
  simp only [logDetNoise, LocalProcess.observableNoise, LocalProcess.noise, Probability.stopped]
  by_cases ht : (t : WithTop ℝ) ≤ D.exit ω
  · simp only [ht, ite_true, logDetNoiseCoefficient_eq_sum hμ hfull]
  · simp only [ht, ite_false, mul_zero, Finset.sum_const_zero]

theorem logDetNoise_admissible (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (k : Fin n) :
    Measurable (Function.uncurry (D.logDetNoise k)) ∧
    Probability.ProgressivelyMeasurable ℱ (D.logDetNoise k) ∧
    ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ t in Icc (0 : ℝ) T,
      (‖D.logDetNoise k ω t‖₊ : ℝ≥0∞)^2 ∂volume ∂P < ⊤ := by
  have hf := contDiff_coordinateLogDet hμ hfull
  obtain ⟨hm, hp, hq, _⟩ := exists_stochasticIntegralBrownian_finsetSum (W.W k) ℱ (hW k)
    (fun a : Fin (n+n*n) => D.observableNoise (coordinateLogDetGradient μ) a k)
    (fun a => D.observableNoise_measurable _ (contDiff_coordinateLogDetGradient hμ hfull).continuous a k)
    (fun a => D.observableNoise_progressive _ (contDiff_coordinateLogDetGradient hμ hfull).continuous a k)
    (fun a => D.smoothObservableNoise_energy (coordinateLogDet μ) hf a k)
    Finset.univ (by norm_num : (0 : ℝ) < 1)
  rw [D.logDetNoise_eq_sum hμ hfull]
  exact ⟨hm, hp, hq⟩

def logDetNoiseIntegral (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (k : Fin n) (T : ℝ) : Ω → ℝ :=
  stochasticIntegralBrownian (W.W k) ℱ (hW k) (D.logDetNoise k)
    (D.logDetNoise_admissible hμ hfull k).1 (D.logDetNoise_admissible hμ hfull k).2.1
    (D.logDetNoise_admissible hμ hfull k).2.2 T

theorem logDetNoiseIntegral_eq_sum (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (k : Fin n)
    {T : ℝ} (hT : 0 < T) : D.logDetNoiseIntegral hμ hfull k T =ᵐ[P]
      fun ω => ∑ a : Fin (n+n*n), D.smoothObservableNoiseIntegral (coordinateLogDet μ)
        (contDiff_coordinateLogDet hμ hfull) a k T ω := by
  have hf := contDiff_coordinateLogDet hμ hfull
  obtain ⟨hm, hp, hq, he⟩ := exists_stochasticIntegralBrownian_finsetSum (W.W k) ℱ (hW k)
    (fun a : Fin (n+n*n) => D.observableNoise (coordinateLogDetGradient μ) a k)
    (fun a => D.observableNoise_measurable _ (contDiff_coordinateLogDetGradient hμ hfull).continuous a k)
    (fun a => D.observableNoise_progressive _ (contDiff_coordinateLogDetGradient hμ hfull).continuous a k)
    (fun a => D.smoothObservableNoise_energy (coordinateLogDet μ) hf a k)
    Finset.univ hT
  unfold logDetNoiseIntegral
  rw [stochasticIntegralBrownian_congr_fun (W.W k) ℱ (hW k) (D.logDetNoise_eq_sum hμ hfull k)
    (D.logDetNoise_admissible hμ hfull k).1 (D.logDetNoise_admissible hμ hfull k).2.1
    (D.logDetNoise_admissible hμ hfull k).2.2 hm hp hq T]
  exact he

/-- This is the log determinant of the actual covariance, with actual stopped
Brownian trace coefficients and exact negative drift. -/
theorem logDet_equation (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[ℱ 0] A)
    {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, (T : WithTop ℝ) ≤ D.exit ω →
      Real.log (D.covariancePath T ω).det - Real.log (covariance μ 0 0).det =
        (∫ t in Icc (0 : ℝ) T,
          -(n : ℝ) - 1/2 * logDetTraceCorrection μ (D.pair.Y t ω) ∂volume) +
          ∑ k : Fin n, D.logDetNoiseIntegral hμ hfull k T ω := by
  have hi := D.itoFormula_original_smooth (coordinateLogDet μ)
    (contDiff_coordinateLogDet hμ hfull) hℱ0 hnull hT
  have hg : observableGenerator (coordinateDrift μ) (coordinateDiffusion μ)
      (coordinateLogDetGradient μ) (coordinateLogDetHessian μ) =
      fun z => -(n : ℝ) - 1/2 * logDetTraceCorrection μ z := by
    funext z
    exact observableGenerator_coordinateLogDet hμ hfull z
  have hn : ∀ᵐ ω ∂P, ∀ k : Fin n,
      D.logDetNoiseIntegral hμ hfull k T ω =
        ∑ a : Fin (n+n*n), D.smoothObservableNoiseIntegral (coordinateLogDet μ)
          (contDiff_coordinateLogDet hμ hfull) a k T ω :=
    ae_all_iff.mpr fun k => D.logDetNoiseIntegral_eq_sum hμ hfull k hT
  filter_upwards [hi, D.initial_Y, hn] with ω hI h0 hnoise hle
  have h := hI hle
  change coordinateLogDet μ (D.pair.Y T ω) - coordinateLogDet μ (D.pair.Y 0 ω) =
    (∫ t in Icc (0 : ℝ) T,
      observableGenerator (coordinateDrift μ) (coordinateDiffusion μ)
        (coordinateLogDetGradient μ) (coordinateLogDetHessian μ) (D.pair.Y t ω) ∂volume) + _ at h
  rw [hg] at h
  have hs : (∑ a : Fin (n+n*n), ∑ k : Fin n,
      D.smoothObservableNoiseIntegral (coordinateLogDet μ) (contDiff_coordinateLogDet hμ hfull) a k T ω) =
      ∑ k : Fin n, D.logDetNoiseIntegral hμ hfull k T ω := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => (hnoise k).symm
  rw [hs, h0] at h
  simpa only [coordinateLogDet, coordinateCovarianceMatrix, coordinateCovariance,
    covariancePath, parameterPath, decodeState_zero, Prod.fst_zero, Prod.snd_zero] using h

end BallProcess
end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.BallProcess.logDet_equation

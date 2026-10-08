import KLS.AdaptiveLocalLogDetIto
import KLS.AdaptiveMaximalCovarianceIto

/-! Log-determinant Itô equation evaluated along the actual assembled maximal path. -/
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
namespace KLS.AdaptiveLocalization
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
open LevyStochCalc.Brownian.Ito LevyStochCalc.Ito.Picard KLS.LocalDiffusion KLSLevyProbe
universe u
variable {n : ℕ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {μ : Measure (Space n)} [IsProbabilityMeasure μ]
  {W : MultidimBrownianMotion P n} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ}
namespace MaximalProcess
variable (D : MaximalProcess μ W ℱ hW)

def logDetNoise (m : ℕ) (k : Fin n) : Ω → ℝ → ℝ :=
  Probability.stopped (D.exit m) (fun ω t => logDetNoiseCoefficient μ k (D.path t ω))

include D in
theorem continuous_logDetNoiseCoefficient (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (k : Fin n) : Continuous (logDetNoiseCoefficient μ k) := by
  have he : logDetNoiseCoefficient μ k =
      fun z => coordinateLogDetGradient μ z (coordinateDiffusion μ k z) :=
    funext fun z => (coordinateLogDet_noise hμ hfull z k).symm
  rw [he]
  exact (contDiff_coordinateLogDetGradient hμ hfull).continuous.clm_apply ((D 0).diffusion_continuous k)

theorem logDetNoise_measurable (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (m : ℕ) (k : Fin n) :
    Measurable (Function.uncurry (D.logDetNoise m k)) :=
  Probability.measurable_uncurry_stopped (D.exit_isStoppingTime m)
    ((D.continuous_logDetNoiseCoefficient hμ hfull k).measurable.comp D.measurable_path)

theorem logDetNoise_progressive (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (m : ℕ) (k : Fin n) :
    Probability.ProgressivelyMeasurable ℱ (D.logDetNoise m k) :=
  Probability.ProgressivelyMeasurable.stopped (D.exit_isStoppingTime m)
    (progressivelyMeasurable_comp_state (f := fun _ z => logDetNoiseCoefficient μ k z)
      D.progressive_path ((D.continuous_logDetNoiseCoefficient hμ hfull k).measurable.comp measurable_snd))

theorem logDetNoise_eq_local (m : ℕ) (k : Fin n) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → D.logDetNoise m k ω t =
      BallProcess.logDetNoise (D m) k ω t := by
  filter_upwards [D.ae_path_eq_of_le_exit] with ω hp t ht
  unfold logDetNoise BallProcess.logDetNoise Probability.stopped
  change (if (t : WithTop ℝ) ≤ D.exit m ω then logDetNoiseCoefficient μ k (D.path t ω) else 0) =
    (if (t : WithTop ℝ) ≤ D.exit m ω then logDetNoiseCoefficient μ k ((D m).pair.Y t ω) else 0)
  by_cases he : (t : WithTop ℝ) ≤ D.exit m ω
  · rw [if_pos he, if_pos he, hp m t ht he]
  · rw [if_neg he, if_neg he]

theorem logDetNoise_energy (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (m : ℕ) (k : Fin n) (T : ℝ) (hT : 0 < T) :
    ∫⁻ ω, ∫⁻ t in Icc (0 : ℝ) T,
      (‖D.logDetNoise m k ω t‖₊ : ℝ≥0∞)^2 ∂volume ∂P < ⊤ := by
  have heq : (∫⁻ ω, ∫⁻ t in Icc (0 : ℝ) T,
      (‖D.logDetNoise m k ω t‖₊ : ℝ≥0∞)^2 ∂volume ∂P) =
      ∫⁻ ω, ∫⁻ t in Icc (0 : ℝ) T,
        (‖BallProcess.logDetNoise (D m) k ω t‖₊ : ℝ≥0∞)^2 ∂volume ∂P := by
    apply lintegral_congr_ae
    filter_upwards [D.logDetNoise_eq_local m k] with ω hω
    exact setLIntegral_congr_fun measurableSet_Icc fun t ht => by rw [hω t ht.1]
  rw [heq]
  exact (BallProcess.logDetNoise_admissible (D m) hμ hfull k).2.2 T hT

def logDetNoiseIntegral (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (m : ℕ) (k : Fin n) (T : ℝ) : Ω → ℝ :=
  stochasticIntegralBrownian (W.W k) ℱ (hW k) (D.logDetNoise m k)
    (D.logDetNoise_measurable hμ hfull m k) (D.logDetNoise_progressive hμ hfull m k)
    (D.logDetNoise_energy hμ hfull m k) T

theorem logDetNoiseIntegral_eq_local (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (m : ℕ) (k : Fin n)
    {T : ℝ} (hT : 0 < T) : D.logDetNoiseIntegral hμ hfull m k T =ᵐ[P]
      BallProcess.logDetNoiseIntegral (D m) hμ hfull k T :=
  stochasticIntegral_congr_ae_nonneg (W.W k) ℱ (hW k)
    (D.logDetNoise_measurable hμ hfull m k) (BallProcess.logDetNoise_admissible (D m) hμ hfull k).1
    (D.logDetNoise_progressive hμ hfull m k) (BallProcess.logDetNoise_admissible (D m) hμ hfull k).2.1
    (D.logDetNoise_energy hμ hfull m k) (BallProcess.logDetNoise_admissible (D m) hμ hfull k).2.2
    (D.logDetNoise_eq_local m k) hT

/-- A fixed-horizon identity before each actual state exit. The determinant and
noise use the actual covariance of the assembled maximal process. -/
theorem logDet_equation (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[ℱ 0] A)
    (m : ℕ) {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, (T : WithTop ℝ) ≤ D.exit m ω →
      Real.log (D.covariancePath T ω).det - Real.log (covariance μ 0 0).det =
        (∫ t in Icc (0 : ℝ) T,
          -(n : ℝ) - 1/2 * logDetTraceCorrection μ (D.path t ω) ∂volume) +
          ∑ k : Fin n, D.logDetNoiseIntegral hμ hfull m k T ω := by
  have hn : ∀ᵐ ω ∂P, ∀ k : Fin n, D.logDetNoiseIntegral hμ hfull m k T ω =
      BallProcess.logDetNoiseIntegral (D m) hμ hfull k T ω :=
    ae_all_iff.mpr fun k => D.logDetNoiseIntegral_eq_local hμ hfull m k hT
  filter_upwards [D.ae_path_eq_of_le_exit,
    BallProcess.logDet_equation (D m) hμ hfull hℱ0 hnull hT, hn]
    with ω hp he hnoise hle
  have hc : D.covariancePath T ω = BallProcess.covariancePath (D m) T ω := by
    unfold covariancePath BallProcess.covariancePath parameterPath BallProcess.parameterPath
    rw [hp m T hT.le hle]
  have hd : (∫ t in Icc (0 : ℝ) T,
      -(n : ℝ) - 1/2 * logDetTraceCorrection μ ((D m).pair.Y t ω) ∂volume) =
      ∫ t in Icc (0 : ℝ) T,
      -(n : ℝ) - 1/2 * logDetTraceCorrection μ (D.path t ω) ∂volume := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    dsimp only
    rw [hp m t ht.1 ((show (t : WithTop ℝ) ≤ (T : WithTop ℝ) by exact_mod_cast ht.2).trans hle)]
  have hs : (∑ k : Fin n, BallProcess.logDetNoiseIntegral (D m) hμ hfull k T ω) =
      ∑ k : Fin n, D.logDetNoiseIntegral hμ hfull m k T ω :=
    Finset.sum_congr rfl fun k _ => (hnoise k).symm
  exact ((congrArg (fun A : Matrix (Fin n) (Fin n) ℝ =>
    Real.log A.det - Real.log (covariance μ 0 0).det) hc).trans (he hle)).trans
      (congrArg₂ (fun x y : ℝ => x + y) hd hs)

end MaximalProcess
end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.MaximalProcess.logDet_equation

import KLS.AdaptiveLocalCovarianceIto

/-! Third-cumulant Brownian noise evaluated along the actual maximal path. -/
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
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

def covariancePath (t : ℝ) (ω : Ω) : Matrix (Fin n) (Fin n) ℝ :=
  covariance μ (D.parameterPath t ω).1 (D.parameterPath t ω).2

def covarianceNoise (m : ℕ) (i j k : Fin n) : Ω → ℝ → ℝ :=
  Probability.stopped (D.exit m) (fun ω t => covarianceNoiseCoefficient μ i j k (D.path t ω))

theorem covarianceNoise_eq_thirdCumulant (hμ : IsCompact μ.support) (m : ℕ) (i j k : Fin n) :
    D.covarianceNoise m i j k = Probability.stopped (D.exit m) (fun ω t =>
      tiltThirdCumulant μ (exponent (D.parameterPath t ω).1 (D.parameterPath t ω).2)
        (fun x => x i) (fun x => x j) (projection μ (D.parameterPath t ω) k)) := by
  unfold covarianceNoise
  congr 1
  funext ω t
  exact covarianceNoiseCoefficient_eq_thirdCumulant hμ i j k (D.path t ω)

theorem covarianceNoise_measurable (hμ : IsCompact μ.support) (m : ℕ) (i j k : Fin n) :
    Measurable (Function.uncurry (D.covarianceNoise m i j k)) :=
  Probability.measurable_uncurry_stopped (D.exit_isStoppingTime m)
    ((((contDiff_coordinateCovarianceGradient hμ i j).continuous.clm_apply
      ((D m).diffusion_continuous k)).measurable).comp D.measurable_path)

theorem covarianceNoise_progressive (hμ : IsCompact μ.support) (m : ℕ) (i j k : Fin n) :
    Probability.ProgressivelyMeasurable ℱ (D.covarianceNoise m i j k) :=
  Probability.ProgressivelyMeasurable.stopped (D.exit_isStoppingTime m)
    (progressivelyMeasurable_comp_state (f := fun _ z => covarianceNoiseCoefficient μ i j k z)
      D.progressive_path ((((contDiff_coordinateCovarianceGradient hμ i j).continuous.clm_apply
        ((D m).diffusion_continuous k)).measurable).comp measurable_snd))

theorem covarianceNoise_eq_local (m : ℕ) (i j k : Fin n) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → D.covarianceNoise m i j k ω t =
      BallProcess.covarianceNoise (D m) i j k ω t := by
  filter_upwards [D.ae_path_eq_of_le_exit] with ω hp t ht
  unfold covarianceNoise BallProcess.covarianceNoise Probability.stopped
  change (if (t : WithTop ℝ) ≤ D.exit m ω then covarianceNoiseCoefficient μ i j k (D.path t ω) else 0) =
    (if (t : WithTop ℝ) ≤ D.exit m ω then covarianceNoiseCoefficient μ i j k ((D m).pair.Y t ω) else 0)
  by_cases he : (t : WithTop ℝ) ≤ D.exit m ω
  · rw [if_pos he, if_pos he, hp m t ht he]
  · rw [if_neg he, if_neg he]

theorem covarianceNoise_energy (hμ : IsCompact μ.support) (m : ℕ) (i j k : Fin n)
    (T : ℝ) (hT : 0 < T) :
    ∫⁻ ω, ∫⁻ t in Icc (0 : ℝ) T,
      (‖D.covarianceNoise m i j k ω t‖₊ : ℝ≥0∞)^2 ∂volume ∂P < ⊤ := by
  have heq : (∫⁻ ω, ∫⁻ t in Icc (0 : ℝ) T,
      (‖D.covarianceNoise m i j k ω t‖₊ : ℝ≥0∞)^2 ∂volume ∂P) =
      ∫⁻ ω, ∫⁻ t in Icc (0 : ℝ) T,
        (‖BallProcess.covarianceNoise (D m) i j k ω t‖₊ : ℝ≥0∞)^2 ∂volume ∂P := by
    apply lintegral_congr_ae
    filter_upwards [D.covarianceNoise_eq_local m i j k] with ω hω
    exact setLIntegral_congr_fun measurableSet_Icc fun t ht => by rw [hω t ht.1]
  rw [heq]
  exact (BallProcess.covarianceNoise_admissible (D m) hμ i j k).2.2 T hT

def covarianceNoiseIntegral (hμ : IsCompact μ.support) (m : ℕ) (i j k : Fin n) (T : ℝ) : Ω → ℝ :=
  stochasticIntegralBrownian (W.W k) ℱ (hW k) (D.covarianceNoise m i j k)
    (D.covarianceNoise_measurable hμ m i j k) (D.covarianceNoise_progressive hμ m i j k)
    (D.covarianceNoise_energy hμ m i j k) T

theorem covarianceNoiseIntegral_eq_local (hμ : IsCompact μ.support) (m : ℕ) (i j k : Fin n)
    {T : ℝ} (hT : 0 < T) : D.covarianceNoiseIntegral hμ m i j k T =ᵐ[P]
      BallProcess.covarianceNoiseIntegral (D m) hμ i j k T :=
  stochasticIntegral_congr_ae_nonneg (W.W k) ℱ (hW k)
    (D.covarianceNoise_measurable hμ m i j k) (BallProcess.covarianceNoise_admissible (D m) hμ i j k).1
    (D.covarianceNoise_progressive hμ m i j k) (BallProcess.covarianceNoise_admissible (D m) hμ i j k).2.1
    (D.covarianceNoise_energy hμ m i j k) (BallProcess.covarianceNoise_admissible (D m) hμ i j k).2.2
    (D.covarianceNoise_eq_local m i j k) hT

end MaximalProcess
end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.MaximalProcess.covarianceNoiseIntegral_eq_local

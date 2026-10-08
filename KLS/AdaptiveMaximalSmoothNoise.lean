import KLS.AdaptiveEnergyDriftBound

/-! Genuine localized Brownian noise for every smooth state observable,
along the assembled maximal adaptive path. -/
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
variable (f : (Fin (n+n*n) → ℝ) → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)

def smoothNoise (j : ℕ) (a : Fin (n+n*n)) (k : Fin n) : Ω → ℝ → ℝ :=
  Probability.stopped (D.exit j) (fun ω t =>
    coordDeriv (fderiv ℝ f) a (D.path t ω) * coordinateDiffusion μ k (D.path t ω) a)

include hf

include D in
theorem smoothNoiseCoefficient_continuous (a : Fin (n+n*n)) (k : Fin n) :
    Continuous (fun z => coordDeriv (fderiv ℝ f) a z * coordinateDiffusion μ k z a) :=
  ((hf.continuous_fderiv (by simp)).clm_apply continuous_const).mul
    ((continuous_apply a).comp ((D 0).diffusion_continuous k))

theorem smoothNoise_measurable (j : ℕ) (a : Fin (n+n*n)) (k : Fin n) :
    Measurable (Function.uncurry (D.smoothNoise f j a k)) :=
  Probability.measurable_uncurry_stopped (D.exit_isStoppingTime j)
    ((D.smoothNoiseCoefficient_continuous f hf a k).measurable.comp D.measurable_path)

theorem smoothNoise_progressive (j : ℕ) (a : Fin (n+n*n)) (k : Fin n) :
    Probability.ProgressivelyMeasurable ℱ (D.smoothNoise f j a k) :=
  Probability.ProgressivelyMeasurable.stopped (D.exit_isStoppingTime j)
    (progressivelyMeasurable_comp_state
      (f := fun _ z => coordDeriv (fderiv ℝ f) a z * coordinateDiffusion μ k z a)
      D.progressive_path ((D.smoothNoiseCoefficient_continuous f hf a k).measurable.comp measurable_snd))

omit hf in
theorem smoothNoise_eq_local (j : ℕ) (a : Fin (n+n*n)) (k : Fin n) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → D.smoothNoise f j a k ω t =
      (D j).observableNoise (fderiv ℝ f) a k ω t := by
  filter_upwards [D.ae_path_eq_of_le_exit] with ω hp t ht
  unfold smoothNoise LocalProcess.observableNoise LocalProcess.noise Probability.stopped
  change (if (t : WithTop ℝ) ≤ D.exit j ω then _ else 0) =
    _ * (if (t : WithTop ℝ) ≤ D.exit j ω then _ else 0)
  by_cases he : (t : WithTop ℝ) ≤ D.exit j ω
  · simp only [he, ite_true]
    rw [hp j t ht he]
  · simp only [he, ite_false, mul_zero]

theorem smoothNoise_energy (j : ℕ) (a : Fin (n+n*n)) (k : Fin n) (T : ℝ) (hT : 0 < T) :
    ∫⁻ ω, ∫⁻ t in Icc (0 : ℝ) T,
      (‖D.smoothNoise f j a k ω t‖₊ : ℝ≥0∞)^2 ∂volume ∂P < ⊤ := by
  have he : (∫⁻ ω, ∫⁻ t in Icc (0 : ℝ) T,
      (‖D.smoothNoise f j a k ω t‖₊ : ℝ≥0∞)^2 ∂volume ∂P) =
      ∫⁻ ω, ∫⁻ t in Icc (0 : ℝ) T,
      (‖(D j).observableNoise (fderiv ℝ f) a k ω t‖₊ : ℝ≥0∞)^2 ∂volume ∂P := by
    apply lintegral_congr_ae
    filter_upwards [D.smoothNoise_eq_local f j a k] with ω hω
    exact setLIntegral_congr_fun measurableSet_Icc fun t ht => by rw [hω t ht.1]
  rw [he]
  exact (D j).smoothObservableNoise_energy f hf a k T hT

def smoothNoiseIntegral (j : ℕ) (a : Fin (n+n*n)) (k : Fin n) (T : ℝ) : Ω → ℝ :=
  stochasticIntegralBrownian (W.W k) ℱ (hW k) (D.smoothNoise f j a k)
    (D.smoothNoise_measurable f hf j a k) (D.smoothNoise_progressive f hf j a k)
    (D.smoothNoise_energy f hf j a k) T

theorem smoothNoiseIntegral_martingale (j : ℕ) (a : Fin (n+n*n)) (k : Fin n) :
    Martingale (D.smoothNoiseIntegral f hf j a k) ℱ P :=
  martingale_stochasticIntegralBrownian (W.W k) ℱ (hW k) (D.smoothNoise f j a k)
    (D.smoothNoise_measurable f hf j a k) (D.smoothNoise_progressive f hf j a k)
    (D.smoothNoise_energy f hf j a k)

theorem smoothNoiseIntegral_eq_local (j : ℕ) (a : Fin (n+n*n)) (k : Fin n)
    {T : ℝ} (hT : 0 < T) : D.smoothNoiseIntegral f hf j a k T =ᵐ[P]
      (D j).smoothObservableNoiseIntegral f hf a k T :=
  stochasticIntegral_congr_ae_nonneg (W.W k) ℱ (hW k)
    (D.smoothNoise_measurable f hf j a k)
    ((D j).observableNoise_measurable _ (hf.continuous_fderiv (by simp)) a k)
    (D.smoothNoise_progressive f hf j a k)
    ((D j).observableNoise_progressive _ (hf.continuous_fderiv (by simp)) a k)
    (D.smoothNoise_energy f hf j a k) ((D j).smoothObservableNoise_energy f hf a k)
    (D.smoothNoise_eq_local f j a k) hT

end MaximalProcess
end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.MaximalProcess.smoothNoiseIntegral_martingale
#print axioms KLS.AdaptiveLocalization.MaximalProcess.smoothNoiseIntegral_eq_local

import KLS.AdaptiveLocalCumulantIto
import KLS.AdaptiveLowerCumulantDriftInner

/-! Genuine next-cumulant Brownian integrals along the actual maximal localization path. -/
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
variable (D : MaximalProcess μ W ℱ hW) (m : ℕ) (h : Fin m → Space n)

def cumulantPath (t : ℝ) (ω : Ω) : ℝ := cumulantTensor (D.localizationLaw t ω) m h

def cumulantNoise (r : ℕ) (k : Fin n) : Ω → ℝ → ℝ :=
  Probability.stopped (D.exit r) (fun ω t => cumulantNoiseCoefficient μ m h k (D.path t ω))

include D in
theorem cumulantNoiseCoefficient_continuous (hμ : IsCompact μ.support) (hm : m ≠ 0)
    (k : Fin n) : Continuous (cumulantNoiseCoefficient μ m h k) := by
  have he : cumulantNoiseCoefficient μ m h k =
      fun z => coordinateCumulantGradient μ m h z (coordinateDiffusion μ k z) :=
    funext fun z => (coordinateCumulantGradient_diffusion hμ hm h z k).symm
  rw [he]
  exact (contDiff_coordinateCumulantGradient m h hμ hm).continuous.clm_apply
    ((D 0).diffusion_continuous k)

theorem cumulantNoise_measurable (hμ : IsCompact μ.support) (hm : m ≠ 0)
    (r : ℕ) (k : Fin n) : Measurable (Function.uncurry (D.cumulantNoise m h r k)) :=
  Probability.measurable_uncurry_stopped (D.exit_isStoppingTime r)
    ((D.cumulantNoiseCoefficient_continuous m h hμ hm k).measurable.comp D.measurable_path)

theorem cumulantNoise_progressive (hμ : IsCompact μ.support) (hm : m ≠ 0)
    (r : ℕ) (k : Fin n) : Probability.ProgressivelyMeasurable ℱ (D.cumulantNoise m h r k) :=
  Probability.ProgressivelyMeasurable.stopped (D.exit_isStoppingTime r)
    (progressivelyMeasurable_comp_state (f := fun _ z => cumulantNoiseCoefficient μ m h k z)
      D.progressive_path ((D.cumulantNoiseCoefficient_continuous m h hμ hm k).measurable.comp measurable_snd))

theorem cumulantNoise_eq_local (r : ℕ) (k : Fin n) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → D.cumulantNoise m h r k ω t =
      BallProcess.cumulantNoise m h (D r) k ω t := by
  filter_upwards [D.ae_path_eq_of_le_exit] with ω hp t ht
  unfold cumulantNoise BallProcess.cumulantNoise Probability.stopped
  change (if (t : WithTop ℝ) ≤ D.exit r ω then cumulantNoiseCoefficient μ m h k (D.path t ω) else 0) =
    (if (t : WithTop ℝ) ≤ D.exit r ω then cumulantNoiseCoefficient μ m h k ((D r).pair.Y t ω) else 0)
  by_cases he : (t : WithTop ℝ) ≤ D.exit r ω
  · rw [if_pos he, if_pos he, hp r t ht he]
  · rw [if_neg he, if_neg he]

theorem cumulantNoise_energy (hμ : IsCompact μ.support) (hm : m ≠ 0)
    (r : ℕ) (k : Fin n) (T : ℝ) (hT : 0 < T) :
    ∫⁻ ω, ∫⁻ t in Icc (0 : ℝ) T,
      (‖D.cumulantNoise m h r k ω t‖₊ : ℝ≥0∞)^2 ∂volume ∂P < ⊤ := by
  have heq : (∫⁻ ω, ∫⁻ t in Icc (0 : ℝ) T,
      (‖D.cumulantNoise m h r k ω t‖₊ : ℝ≥0∞)^2 ∂volume ∂P) =
      ∫⁻ ω, ∫⁻ t in Icc (0 : ℝ) T,
        (‖BallProcess.cumulantNoise m h (D r) k ω t‖₊ : ℝ≥0∞)^2 ∂volume ∂P := by
    apply lintegral_congr_ae
    filter_upwards [D.cumulantNoise_eq_local m h r k] with ω hω
    exact setLIntegral_congr_fun measurableSet_Icc fun t ht => by rw [hω t ht.1]
  rw [heq]
  exact (BallProcess.cumulantNoise_admissible m h (D r) hμ hm k).2.2 T hT

def cumulantNoiseIntegral (hμ : IsCompact μ.support) (hm : m ≠ 0)
    (r : ℕ) (k : Fin n) (T : ℝ) : Ω → ℝ :=
  stochasticIntegralBrownian (W.W k) ℱ (hW k) (D.cumulantNoise m h r k)
    (D.cumulantNoise_measurable m h hμ hm r k) (D.cumulantNoise_progressive m h hμ hm r k)
    (D.cumulantNoise_energy m h hμ hm r k) T

theorem cumulantNoiseIntegral_martingale (hμ : IsCompact μ.support) (hm : m ≠ 0)
    (r : ℕ) (k : Fin n) : Martingale (D.cumulantNoiseIntegral m h hμ hm r k) ℱ P :=
  martingale_stochasticIntegralBrownian (W.W k) ℱ (hW k) (D.cumulantNoise m h r k)
    (D.cumulantNoise_measurable m h hμ hm r k) (D.cumulantNoise_progressive m h hμ hm r k)
    (D.cumulantNoise_energy m h hμ hm r k)

theorem cumulantNoiseIntegral_eq_local (hμ : IsCompact μ.support) (hm : m ≠ 0)
    (r : ℕ) (k : Fin n) {T : ℝ} (hT : 0 < T) : D.cumulantNoiseIntegral m h hμ hm r k T =ᵐ[P]
      BallProcess.cumulantNoiseIntegral m h (D r) hμ hm k T :=
  stochasticIntegral_congr_ae_nonneg (W.W k) ℱ (hW k)
    (D.cumulantNoise_measurable m h hμ hm r k) (BallProcess.cumulantNoise_admissible m h (D r) hμ hm k).1
    (D.cumulantNoise_progressive m h hμ hm r k) (BallProcess.cumulantNoise_admissible m h (D r) hμ hm k).2.1
    (D.cumulantNoise_energy m h hμ hm r k) (BallProcess.cumulantNoise_admissible m h (D r) hμ hm k).2.2
    (D.cumulantNoise_eq_local m h r k) hT

end MaximalProcess
end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.MaximalProcess.cumulantNoiseIntegral_eq_local
#print axioms KLS.AdaptiveLocalization.MaximalProcess.cumulantNoiseIntegral_martingale

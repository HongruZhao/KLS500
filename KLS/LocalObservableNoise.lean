import KLS.LocalProcessEquation
import KLS.DiffusionUnboundedIto

/-! Actual stopped Brownian integrands for smooth local observables. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology
noncomputable section
namespace KLS.LocalDiffusion.LocalProcess
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
open LevyStochCalc.Brownian.Ito LevyStochCalc.Ito.Setting LevyStochCalc.Ito.Picard
open KLSLevyAdapter KLSLevyProbe
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {N d : ℕ} {W : MultidimBrownianMotion P d} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ}
  {b : (Fin N → ℝ) → Fin N → ℝ} {s : Fin d → (Fin N → ℝ) → Fin N → ℝ} {R : ℝ}
  (D : LocalProcess W ℱ hW b s R)
  (f' : (Fin N → ℝ) → (Fin N → ℝ) →L[ℝ] ℝ)

def observableNoise (i : Fin N) (k : Fin d) : Ω → ℝ → ℝ :=
  fun ω t => coordDeriv f' i (D.pair.Y t ω) * D.noise i k ω t

theorem observableNoise_measurable (hc : Continuous f') (i : Fin N) (k : Fin d) :
    Measurable (Function.uncurry (D.observableNoise f' i k)) :=
  (D.pair.ito_Y.measurable_uncurry_comp (continuous_coordDeriv hc i).measurable).mul
    (D.noise_measurable i k)

theorem observableNoise_progressive (hc : Continuous f') (i : Fin N) (k : Fin d) :
    Probability.ProgressivelyMeasurable ℱ (D.observableNoise f' i k) :=
  (D.pair.ito_Y.progressivelyMeasurable_comp (continuous_coordDeriv hc i)).mul
    (D.noise_progressive i k)

theorem observableNoise_energy {K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ z, ‖f' z‖ ≤ K)
    (i : Fin N) (k : Fin d) (T : ℝ) (hT : 0 < T) :
    ∫⁻ ω, ∫⁻ t in Icc (0 : ℝ) T,
      (‖D.observableNoise f' i k ω t‖₊ : ℝ≥0∞)^2 ∂volume ∂P < ⊤ :=
  lintegral_sq_bounded_mul_lt_top (D.noise_energy i k) hK0
    (fun ω t => abs_coordDeriv_le hK i (D.pair.Y t ω)) T hT

def observableNoiseIntegral (hc : Continuous f') {K : ℝ}
    (hK0 : 0 ≤ K) (hK : ∀ z, ‖f' z‖ ≤ K) (i : Fin N) (k : Fin d) (T : ℝ) : Ω → ℝ :=
  stochasticIntegralBrownian (W.W k) ℱ (hW k) (D.observableNoise f' i k)
    (D.observableNoise_measurable f' hc i k) (D.observableNoise_progressive f' hc i k)
    (D.observableNoise_energy f' hK0 hK i k) T

theorem observableNoiseIntegral_eq_before_exit (hc : Continuous f') {K : ℝ}
    (hK0 : 0 ≤ K) (hK : ∀ z, ‖f' z‖ ≤ K) (i : Fin N) (k : Fin d) {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, (T : WithTop ℝ) ≤ D.exit ω →
      D.observableNoiseIntegral f' hc hK0 hK i k T ω =
        stochasticIntegralBrownian (W.W k) ℱ (hW k)
          (fun ω t => coordDeriv f' i (D.pair.Y t ω) * D.extension.σ t (D.pair.X t ω) i k)
          (D.pair.weighted_diffusion_measurable hc i k)
          (D.pair.weighted_diffusion_progressive hc i k)
          (D.pair.weighted_diffusion_energy hK0 hK i k) T ω := by
  let H : Ω → ℝ → ℝ := fun ω t =>
    coordDeriv f' i (D.pair.Y t ω) * D.extension.σ t (D.pair.X t ω) i k
  have hm := D.pair.weighted_diffusion_measurable hc i k
  have hp := D.pair.weighted_diffusion_progressive hc i k
  have hq := D.pair.weighted_diffusion_energy hK0 hK i k
  have hms : Measurable (Function.uncurry (Probability.stopped D.exit H)) :=
    Probability.measurable_uncurry_stopped D.exit_isStoppingTime hm
  have hps : Probability.ProgressivelyMeasurable ℱ (Probability.stopped D.exit H) :=
    hp.stopped D.exit_isStoppingTime
  have hqs : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ t in Icc (0 : ℝ) T,
      (‖Probability.stopped D.exit H ω t‖₊ : ℝ≥0∞)^2 ∂volume ∂P < ⊤ :=
    energy_lt_top_of_abs_le (fun ω t => Probability.abs_stopped_le D.exit H ω t) hq
  have he : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → D.observableNoise f' i k ω t =
      Probability.stopped D.exit H ω t := by
    filter_upwards [D.noise_eq_stopped_extension i k] with ω hω t ht
    unfold observableNoise
    rw [hω t ht]
    unfold Probability.stopped H
    change _ * (if (t : WithTop ℝ) ≤ D.exit ω then _ else 0) =
      (if (t : WithTop ℝ) ≤ D.exit ω then _ else 0)
    split_ifs <;> simp
  have hi := stochasticIntegral_congr_ae_nonneg (W.W k) ℱ (hW k)
    (D.observableNoise_measurable f' hc i k) hms
    (D.observableNoise_progressive f' hc i k) hps
    (D.observableNoise_energy f' hK0 hK i k) hqs he hT
  have hs := stochasticIntegralBrownian_stopped_eq_of_le D.exit (W.W k) ℱ (hW k)
    D.exit_isStoppingTime hm hp hq hT
  filter_upwards [hi, hs] with ω hiω hsω hle
  exact hiω.trans (hsω hle)

end KLS.LocalDiffusion.LocalProcess
end
#print axioms KLS.LocalDiffusion.LocalProcess.observableNoiseIntegral_eq_before_exit

import KLS.LocalProcessEquation
import KLS.DiffusionUnboundedIto
import LevyStochCalc.Ito.VectorItoProcessDiff

/-! Stopped Itô representations of the actual constructed local processes. -/
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
  (D : LocalProcess W ℱ hW b s R) (τ : Ω → WithTop ℝ) (hτ : IsStoppingTime ℱ τ)

def stoppedDrift (i : Fin N) : Ω → ℝ → ℝ :=
  Probability.stopped τ (fun ω t => D.extension.μ t (D.pair.X t ω) i)

def stoppedDiffusion (i : Fin N) (k : Fin d) : Ω → ℝ → ℝ :=
  Probability.stopped τ (fun ω t => D.extension.σ t (D.pair.X t ω) i k)

include hτ in
theorem stoppedDrift_measurable (i : Fin N) :
    Measurable (Function.uncurry (D.stoppedDrift τ i)) :=
  Probability.measurable_uncurry_stopped hτ (D.pair.drift_measurable D.regular i)

theorem stoppedDrift_energy (i : Fin N) (T : ℝ) (hT : 0 < T) :
    ∫⁻ ω, ∫⁻ t in Icc (0 : ℝ) T,
      (‖D.stoppedDrift τ i ω t‖₊ : ℝ≥0∞)^2 ∂volume ∂P < ⊤ := by
  obtain ⟨L, hL⟩ := D.lipschitz
  exact energy_lt_top_of_abs_le (fun ω t => Probability.abs_stopped_le τ _ ω t)
    (D.pair.drift_energy D.regular hL i) T hT

include hτ in
theorem stoppedDiffusion_measurable (i : Fin N) (k : Fin d) :
    Measurable (Function.uncurry (D.stoppedDiffusion τ i k)) :=
  Probability.measurable_uncurry_stopped hτ ((D.pair.solves_X 0).h_σ_meas i k)

include hτ in
theorem stoppedDiffusion_progressive (i : Fin N) (k : Fin d) :
    Probability.ProgressivelyMeasurable ℱ (D.stoppedDiffusion τ i k) :=
  Probability.ProgressivelyMeasurable.stopped hτ ((D.pair.solves_X 0).h_σ_progMeas i k)

theorem stoppedDiffusion_energy (i : Fin N) (k : Fin d) (T : ℝ) (hT : 0 < T) :
    ∫⁻ ω, ∫⁻ t in Icc (0 : ℝ) T,
      (‖D.stoppedDiffusion τ i k ω t‖₊ : ℝ≥0∞)^2 ∂volume ∂P < ⊤ :=
  energy_lt_top_of_abs_le (fun ω t => Probability.abs_stopped_le τ _ ω t)
    ((D.pair.solves_X 0).h_σ_sq i k) T hT

def stoppedIto (T : ℝ) : Ω → Fin N → ℝ :=
  vectorItoProcess W ℱ hW (D.stoppedDiffusion τ)
    (D.stoppedDiffusion_measurable τ hτ) (D.stoppedDiffusion_progressive τ hτ)
    (D.stoppedDiffusion_energy τ) 0 (D.stoppedDrift τ) T

theorem stoppedIto_eq_before {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, (T : WithTop ℝ) ≤ τ ω → D.stoppedIto τ hτ T ω = D.pair.Y T ω := by
  have hn : ∀ᵐ ω ∂P, ∀ i : Fin N, ∀ k : Fin d, (T : WithTop ℝ) ≤ τ ω →
      stochasticIntegralBrownian (W.W k) ℱ (hW k) (D.stoppedDiffusion τ i k)
        (D.stoppedDiffusion_measurable τ hτ i k) (D.stoppedDiffusion_progressive τ hτ i k)
        (D.stoppedDiffusion_energy τ i k) T ω =
      stochasticIntegralBrownian (W.W k) ℱ (hW k)
        (fun ω t => D.extension.σ t (D.pair.X t ω) i k)
        ((D.pair.solves_X 0).h_σ_meas i k) ((D.pair.solves_X 0).h_σ_progMeas i k)
        ((D.pair.solves_X 0).h_σ_sq i k) T ω :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun k =>
      stochasticIntegralBrownian_stopped_eq_of_le τ (W.W k) ℱ (hW k) hτ
        ((D.pair.solves_X 0).h_σ_meas i k) ((D.pair.solves_X 0).h_σ_progMeas i k)
        ((D.pair.solves_X 0).h_σ_sq i k) hT
  filter_upwards [D.pair.ito_Y.ae_eq T hT.le, hn] with ω hI hnoise hle
  rw [hI]
  funext i
  simp only [stoppedIto, vectorItoProcess, vectorItoMartingale, coordItoIntegral,
    Pi.zero_apply, zero_add]
  congr 1
  · apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    exact if_pos ((show (t : WithTop ℝ) ≤ (T : WithTop ℝ) by exact_mod_cast ht.2).trans hle)
  · exact Finset.sum_congr rfl fun k _ => hnoise i k hle

end KLS.LocalDiffusion.LocalProcess
end
#print axioms KLS.LocalDiffusion.LocalProcess.stoppedIto_eq_before

import KLS.AdaptivePathCoefficientBounds

/-! Bounded scalar clips of the original coefficients along the maximal path. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology
noncomputable section
namespace KLS.LocalDiffusion.LocalProcessFamily
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
open LevyStochCalc.Brownian.Ito LevyStochCalc.Ito.Picard
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {N d : ℕ} {W : MultidimBrownianMotion P d} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ}
  {b : (Fin N → ℝ) → Fin N → ℝ} {s : Fin d → (Fin N → ℝ) → Fin N → ℝ}
  (D : LocalProcessFamily W ℱ hW b s)

/-- The product uses its standard maximum norm. -/
def coefficientVector (D : LocalProcessFamily W ℱ hW b s) (z : Fin N → ℝ) : (Fin N → ℝ) × (Fin d → Fin N → ℝ) :=
  (b z, fun k => s k z)

def coefficientClipRadius (L : ℕ) : ℝ := (L : ℝ) + ‖D.coefficientVector 0‖ + 1

theorem coefficientClipRadius_nonneg (L : ℕ) : 0 ≤ D.coefficientClipRadius L := by
  unfold coefficientClipRadius
  positivity

theorem continuous_coefficientVector : Continuous D.coefficientVector :=
  (D 0).drift_continuous.prodMk (continuous_pi fun k => (D 0).diffusion_continuous k)

def clippedNoise (L : ℕ) (i : Fin N) (k : Fin d) : Ω → ℝ → ℝ :=
  fun ω t => clampScalar (D.coefficientClipRadius L) (s k (D.path t ω) i)

def clippedDrift (L : ℕ) (i : Fin N) : Ω → ℝ → ℝ :=
  fun ω t => clampScalar (D.coefficientClipRadius L) (b (D.path t ω) i)

theorem clippedNoise_bound (L : ℕ) (i : Fin N) (k : Fin d) (ω : Ω) (t : ℝ) :
    |D.clippedNoise L i k ω t| ≤ D.coefficientClipRadius L :=
  abs_clampScalar_le (D.coefficientClipRadius_nonneg L) _

theorem clippedDrift_bound (L : ℕ) (i : Fin N) (ω : Ω) (t : ℝ) :
    |D.clippedDrift L i ω t| ≤ D.coefficientClipRadius L :=
  abs_clampScalar_le (D.coefficientClipRadius_nonneg L) _

theorem clippedNoise_measurable (L : ℕ) (i : Fin N) (k : Fin d) :
    Measurable (Function.uncurry (D.clippedNoise L i k)) :=
  ((continuous_clampScalar _).comp ((continuous_apply i).comp ((D 0).diffusion_continuous k))).measurable.comp
    D.measurable_path

theorem clippedNoise_progressive (L : ℕ) (i : Fin N) (k : Fin d) :
    Probability.ProgressivelyMeasurable ℱ (D.clippedNoise L i k) :=
  progressivelyMeasurable_comp_state
    (f := fun _ z => clampScalar (D.coefficientClipRadius L) (s k z i)) D.progressive_path
    (((continuous_clampScalar _).comp ((continuous_apply i).comp ((D 0).diffusion_continuous k))).measurable.comp measurable_snd)

theorem clippedNoise_energy (L : ℕ) (i : Fin N) (k : Fin d) (T : ℝ) (hT : 0 < T) :
    (∫⁻ ω, ∫⁻ t in Icc (0 : ℝ) T, (‖D.clippedNoise L i k ω t‖₊ : ℝ≥0∞)^2 ∂volume ∂P) < ⊤ :=
  energy_lt_top_of_bounded (D.clippedNoise_bound L i k) T hT

def clippedNoiseIntegral (L : ℕ) (i : Fin N) (k : Fin d) (T : ℝ) : Ω → ℝ :=
  stochasticIntegralBrownian (W.W k) ℱ (hW k) (D.clippedNoise L i k)
    (D.clippedNoise_measurable L i k) (D.clippedNoise_progressive L i k) (D.clippedNoise_energy L i k) T

theorem clippedDrift_measurable (L : ℕ) (i : Fin N) :
    Measurable (Function.uncurry (D.clippedDrift L i)) :=
  ((continuous_clampScalar _).comp ((continuous_apply i).comp (D 0).drift_continuous)).measurable.comp D.measurable_path

end KLS.LocalDiffusion.LocalProcessFamily
end
#print axioms KLS.LocalDiffusion.LocalProcessFamily.clippedNoise_energy

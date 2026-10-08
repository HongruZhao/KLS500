import KLS.DiffusionStopping
import LevyStochCalc.Brownian.ItoLocality

/-! Stopping the actual diffusion integrand leaves its Brownian integral unchanged
before the norm-exit time of the constructed continuous representative. -/
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace KLSLevyAdapter.GlobalDiffusionPair
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
open LevyStochCalc.Brownian.Ito LevyStochCalc.Ito.Setting

universe u v
variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {n d : ℕ}
  {W : MultidimBrownianMotion P d} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ} {coeffs : JumpDiffusionCoeffs n d E}
  {x₀ : Fin n → ℝ} (D : GlobalDiffusionPair W ℱ hW coeffs x₀)

theorem stopped_diffusion_integral_eq_before_exit (r : ℝ) (i : Fin n) (k : Fin d)
    {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, (T : WithTop ℝ) ≤ D.exit r ω →
      stochasticIntegralBrownian (W.W k) ℱ (hW k)
        (Probability.stopped (D.exit r) (fun ω s => coeffs.σ s (D.X s ω) i k))
        (D.stopped_diffusion_measurable r i k) (D.stopped_diffusion_progressive r i k)
        (D.stopped_diffusion_energy r i k) T ω =
      stochasticIntegralBrownian (W.W k) ℱ (hW k) (fun ω s => coeffs.σ s (D.X s ω) i k)
        ((D.solves_X 0).h_σ_meas i k) ((D.solves_X 0).h_σ_progMeas i k)
        ((D.solves_X 0).h_σ_sq i k) T ω :=
  stochasticIntegralBrownian_stopped_eq_of_le (D.exit r) (W.W k) ℱ (hW k) (D.exit_isStoppingTime r)
    ((D.solves_X 0).h_σ_meas i k) ((D.solves_X 0).h_σ_progMeas i k)
    ((D.solves_X 0).h_σ_sq i k) hT

#print axioms stopped_diffusion_integral_eq_before_exit
end KLSLevyAdapter.GlobalDiffusionPair

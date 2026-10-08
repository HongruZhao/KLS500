import KLS.LocalProcessConstruction
import KLS.BrownianIntegralAE

/-! The actual original-coefficient SDE holds before the genuine local exit time. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology
noncomputable section
namespace KLS.LocalDiffusion.LocalProcess
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
open LevyStochCalc.Brownian.Ito LevyStochCalc.Ito.Setting
open KLSLevyAdapter KLSLevyProbe
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {N d : ℕ} {W : MultidimBrownianMotion P d} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ}
  {b : (Fin N → ℝ) → Fin N → ℝ} {s : Fin d → (Fin N → ℝ) → Fin N → ℝ} {R : ℝ}
  (D : LocalProcess W ℱ hW b s R)

def noiseIntegral (i : Fin N) (k : Fin d) (T : ℝ) : Ω → ℝ :=
  stochasticIntegralBrownian (W.W k) ℱ (hW k) (D.noise i k)
    (D.noise_measurable i k) (D.noise_progressive i k) (D.noise_energy i k) T

theorem noiseIntegral_eq_before_exit (i : Fin N) (k : Fin d) {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, (T : WithTop ℝ) ≤ D.exit ω →
      D.noiseIntegral i k T ω = stochasticIntegralBrownian (W.W k) ℱ (hW k)
        (fun ω t => D.extension.σ t (D.pair.X t ω) i k)
        ((D.pair.solves_X 0).h_σ_meas i k) ((D.pair.solves_X 0).h_σ_progMeas i k)
        ((D.pair.solves_X 0).h_σ_sq i k) T ω := by
  have heq := stochasticIntegral_congr_ae_nonneg (W.W k) ℱ (hW k)
    (D.noise_measurable i k) (D.pair.stopped_diffusion_measurable R i k)
    (D.noise_progressive i k) (D.pair.stopped_diffusion_progressive R i k)
    (D.noise_energy i k) (D.pair.stopped_diffusion_energy R i k)
    (D.noise_eq_stopped_extension i k) hT
  filter_upwards [heq, D.pair.stopped_diffusion_integral_eq_before_exit R i k hT]
    with ω hω hstop hle
  exact hω.trans (hstop hle)

/-- The literal local SDE, with the original drift and Brownian integrals of the
original diffusion stopped at the norm-exit time. Exceptional sets may depend on T. -/
def OriginalEquation (T : ℝ) : Prop :=
  ∀ᵐ ω ∂P, (T : WithTop ℝ) ≤ D.exit ω → ∀ i : Fin N,
    D.pair.Y T ω i = (∫ t in Set.Icc (0 : ℝ) T, b (D.pair.Y t ω) i ∂volume) +
      ∑ k : Fin d, D.noiseIntegral i k T ω

theorem originalEquation {T : ℝ} (hT : 0 < T) : D.OriginalEquation T := by
  have hn : ∀ᵐ ω ∂P, ∀ i : Fin N, ∀ k : Fin d, (T : WithTop ℝ) ≤ D.exit ω →
      D.noiseIntegral i k T ω = stochasticIntegralBrownian (W.W k) ℱ (hW k)
        (fun ω t => D.extension.σ t (D.pair.X t ω) i k)
        ((D.pair.solves_X 0).h_σ_meas i k) ((D.pair.solves_X 0).h_σ_progMeas i k)
        ((D.pair.solves_X 0).h_σ_sq i k) T ω :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun k => D.noiseIntegral_eq_before_exit i k hT
  filter_upwards [D.pair.ito_Y.ae_eq T hT.le, D.original_coefficients_before_exit, hn]
    with ω hI hcoef hnoise hle i
  have hd : (∫ t in Set.Icc (0 : ℝ) T, D.extension.μ t (D.pair.X t ω) i ∂volume) =
      ∫ t in Set.Icc (0 : ℝ) T, b (D.pair.Y t ω) i ∂volume := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    have hte : (t : WithTop ℝ) ≤ D.exit ω :=
      (show (t : WithTop ℝ) ≤ (T : WithTop ℝ) by exact_mod_cast ht.2).trans hle
    exact congrFun (hcoef t ht.1 hte).1 i
  have hi := congrFun hI i
  simp only [vectorItoProcess, vectorItoMartingale, coordItoIntegral, Pi.zero_apply, zero_add] at hi
  rw [hi, hd]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  exact (hnoise i k hle).symm

end KLS.LocalDiffusion.LocalProcess
end
#print axioms KLS.LocalDiffusion.LocalProcess.originalEquation

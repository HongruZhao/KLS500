import KLS.DiffusionStopping
import LevyStochCalc.Ito.ItoFormulaUnbounded

/-!
Itô calculus for the actual continuous representative constructed with the Picard
solution. Coefficients can be unbounded. A bounded first derivative discharges the
stochastic-integrand energy; no Hessian bound is assumed. Coefficients remain
explicitly evaluated along X, while the observable is evaluated along Y.
-/
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
namespace KLSLevyAdapter.GlobalDiffusionPair
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
open LevyStochCalc.Brownian.Ito LevyStochCalc.Ito.Setting LevyStochCalc.Ito.Picard

universe u v
variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {n d : ℕ}
  {W : MultidimBrownianMotion P d} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ} {coeffs : JumpDiffusionCoeffs n d E}
  {x₀ : Fin n → ℝ} (D : GlobalDiffusionPair W ℱ hW coeffs x₀)

 theorem drift_measurable (hReg : JumpDiffusionCoeffs.IsRegular coeffs (0 : Measure E)) (i : Fin n) :
    Measurable (Function.uncurry fun ω s => coeffs.μ s (D.X s ω) i) :=
  ((measurable_pi_apply i).comp hReg.1).comp
    (measurable_snd.prodMk (D.measurable_X.comp measurable_swap))

theorem drift_progressive (hReg : JumpDiffusionCoeffs.IsRegular coeffs (0 : Measure E)) (i : Fin n) :
    Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.μ s (D.X s ω) i) :=
  progressivelyMeasurable_comp_state (f := fun s x => coeffs.μ s x i) D.progressive_X
    ((measurable_pi_apply i).comp hReg.1)

theorem drift_energy (hReg : JumpDiffusionCoeffs.IsRegular coeffs (0 : Measure E))
    {L : ℝ} (hLip : JumpDiffusionCoeffs.IsLipschitz coeffs (0 : Measure E) L)
    (i : Fin n) (T : ℝ) (hT : 0 < T) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖coeffs.μ s (D.X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
  lintegral_sq_mu_lt_top_of_energy coeffs hReg hLip
    (lintegral_lintegral_sq_lt_top_of_supL2 D.sup_X) i hT

variable {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}

theorem weighted_diffusion_measurable (hf'c : Continuous f') (i : Fin n) (k : Fin d) :
    Measurable (Function.uncurry fun ω s =>
      coordDeriv f' i (D.Y s ω) * coeffs.σ s (D.X s ω) i k) :=
  (D.ito_Y.measurable_uncurry_comp (continuous_coordDeriv hf'c i).measurable).mul
    ((D.solves_X 0).h_σ_meas i k)

theorem weighted_diffusion_progressive (hf'c : Continuous f') (i : Fin n) (k : Fin d) :
    Probability.ProgressivelyMeasurable ℱ (fun ω s =>
      coordDeriv f' i (D.Y s ω) * coeffs.σ s (D.X s ω) i k) :=
  (D.ito_Y.progressivelyMeasurable_comp (continuous_coordDeriv hf'c i)).mul
    ((D.solves_X 0).h_σ_progMeas i k)

theorem weighted_diffusion_energy {K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ z, ‖f' z‖ ≤ K)
    (i : Fin n) (k : Fin d) (T : ℝ) (hT : 0 < T) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖coordDeriv f' i (D.Y s ω) * coeffs.σ s (D.X s ω) i k‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
  lintegral_sq_bounded_mul_lt_top ((D.solves_X 0).h_σ_sq i k) hK0
    (fun ω s => abs_coordDeriv_le hK i (D.Y s ω)) T hT

/-- Genuine unbounded-coefficient Itô identity, with stochastic admissibility proved here. -/
theorem itoFormula_bounded_derivative
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (hReg : JumpDiffusionCoeffs.IsRegular coeffs (0 : Measure E))
    {L : ℝ} (hLip : JumpDiffusionCoeffs.IsLipschitz coeffs (0 : Measure E) L)
    {f : (Fin n → ℝ) → ℝ}
    {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
    (hfC : ContDiff ℝ 2 f) (hf : ∀ z, HasFDerivAt f (f' z) z)
    (hf' : ∀ z, HasFDerivAt f' (f'' z) z) (hf'c : Continuous f')
    {K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ z, ‖f' z‖ ≤ K)
    {T : ℝ} (hT : 0 < T) :
    (fun ω => f (D.Y T ω) - f (D.Y 0 ω)) =ᵐ[P] fun ω =>
      (∑ i : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
          coordDeriv f' i (D.Y s ω) * coeffs.μ s (D.X s ω) i ∂volume)
        + (∑ i : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ (hW k)
            (fun ω s => coordDeriv f' i (D.Y s ω) * coeffs.σ s (D.X s ω) i k)
            (D.weighted_diffusion_measurable hf'c i k)
            (D.weighted_diffusion_progressive hf'c i k)
            (D.weighted_diffusion_energy hK0 hK i k) T ω)
        + 1 / 2 * ∑ i : Fin n, ∑ j : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            coordDeriv₂ f'' i j (D.Y s ω) *
              ∑ k : Fin d, coeffs.σ s (D.X s ω) i k * coeffs.σ s (D.X s ω) j k ∂volume :=
  itoFormula_of_unbounded W ℱ hW D.ito_Y hℱ0 hnull (fun _ => measurable_const)
    (D.drift_measurable hReg) (D.drift_progressive hReg) (D.drift_energy hReg hLip)
    hfC hf hf' (D.weighted_diffusion_measurable hf'c)
    (D.weighted_diffusion_progressive hf'c) (D.weighted_diffusion_energy hK0 hK) hT

#print axioms weighted_diffusion_energy
#print axioms itoFormula_bounded_derivative
end KLSLevyAdapter.GlobalDiffusionPair

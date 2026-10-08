import KLS.ZeroPoisson
import KLS.ZeroJumpContinuous

/-!
Global continuous diffusion existence from the genuine Picard construction.
Acceptance status and source hashes are recorded separately in the replay receipts.
-/
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
namespace KLSLevyProbe
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
open LevyStochCalc.Ito.Setting LevyStochCalc.Ito.Picard

universe u v
variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}

/-- Actual global existence with almost-sure continuous paths for globally Lipschitz
coefficients whose jump coefficient vanishes. The solution is produced by Picard. -/
theorem exists_continuous_globalSolution_of_zeroJump
    (W : MultidimBrownianMotion P d) (N : Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) [ℱ.IsRightContinuous]
    (hW : ∀ k, IsBrownianFiltration (W.W k) ℱ)
    (hN : Poisson.IsPoissonFiltration N ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (coeffs : JumpDiffusionCoeffs n d E)
    (hReg : JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (hγ : ∀ (s : ℝ) (x : Fin n → ℝ) (e : E), coeffs.γ s x e = 0)
    (x₀ : Fin n → ℝ) :
    ∃ X : ℝ → Ω → Fin n → ℝ,
      Measurable (Function.uncurry X) ∧
      (∀ i, Probability.ProgressivelyMeasurable ℱ fun ω s => X s ω i) ∧
      (∀ᵐ ω ∂P, X 0 ω = x₀) ∧
      (∀ᵐ ω ∂P, ContinuousOn (fun t => X t ω) (Set.Ici 0)) ∧
      (∀ T : ℝ, 0 < T →
        ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T,
          ∑ i, (‖X (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤) ∧
      (∀ T, SolvesOn W N ℱ hW hN coeffs x₀ X T) := by
  obtain ⟨X, hXm, hXa, hX0, hXcad, hXS, hsol⟩ :=
    exists_globalSolution W N ℱ hW hN coeffs hℱ0 hnull hReg hLip x₀
  have hRight : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      Tendsto (fun s => X s ω) (nhdsWithin t (Set.Ioi t)) (𝓝 (X t ω)) :=
    hXcad.mono fun _ h t ht => (h t ht).1
  obtain ⟨Y, hY, hXY, hcont⟩ := exists_continuousVersion_of_zeroJump W N ℱ hW hN
    coeffs x₀ X hsol hℱ0 hnull hReg hLip hγ hXm hXa hRight hXS
  exact ⟨X, hXm, hXa, hX0, hcont, hXS, hsol⟩

/-- Brownian diffusion existence with a concrete zero Poisson measure, rather than
an assumed auxiliary jump driver. -/
theorem exists_continuous_globalDiffusion
    (W : MultidimBrownianMotion P d)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) [ℱ.IsRightContinuous]
    (hW : ∀ k, IsBrownianFiltration (W.W k) ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (coeffs : JumpDiffusionCoeffs n d E)
    (hReg : JumpDiffusionCoeffs.IsRegular coeffs (0 : Measure E))
    {L : ℝ} (hLip : JumpDiffusionCoeffs.IsLipschitz coeffs (0 : Measure E) L)
    (hγ : ∀ (s : ℝ) (x : Fin n → ℝ) (e : E), coeffs.γ s x e = 0)
    (x₀ : Fin n → ℝ) :
    ∃ X : ℝ → Ω → Fin n → ℝ,
      Measurable (Function.uncurry X) ∧
      (∀ i, Probability.ProgressivelyMeasurable ℱ fun ω s => X s ω i) ∧
      (∀ᵐ ω ∂P, X 0 ω = x₀) ∧
      (∀ᵐ ω ∂P, ContinuousOn (fun t => X t ω) (Set.Ici 0)) ∧
      (∀ T : ℝ, 0 < T →
        ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T,
          ∑ i, (‖X (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤) ∧
      (∀ T, SolvesOn W (zeroPoisson P) ℱ hW (zeroPoisson_isPoissonFiltration P ℱ)
        coeffs x₀ X T) :=
  exists_continuous_globalSolution_of_zeroJump W (zeroPoisson P) ℱ hW
    (zeroPoisson_isPoissonFiltration P ℱ) hℱ0 hnull coeffs hReg hLip hγ x₀

#print axioms exists_continuous_globalSolution_of_zeroJump
#print axioms exists_continuous_globalDiffusion
end KLSLevyProbe

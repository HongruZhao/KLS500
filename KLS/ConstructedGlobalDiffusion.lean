import KLS.GlobalDiffusion
import KLS.VectorBrownianExample

/-!
Global diffusion existence with the probability space, Brownian driver, and usual
filtration constructed from the accepted Brownian existence theorem. Coefficients
retain the stated measurable, finite-origin-energy and global Lipschitz hypotheses.
-/
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace KLSLevyProbe
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
open LevyStochCalc.Ito.Setting LevyStochCalc.Ito.Picard

/-- The driver and common filtration are supplied by actual Brownian existence. -/
theorem exists_constructed_continuous_globalDiffusion
    {E : Type} [MeasurableSpace E] {n d : ℕ}
    (coeffs : JumpDiffusionCoeffs n d E)
    (hReg : JumpDiffusionCoeffs.IsRegular coeffs (0 : Measure E))
    {L : ℝ} (hLip : JumpDiffusionCoeffs.IsLipschitz coeffs (0 : Measure E) L)
    (hγ : ∀ (s : ℝ) (x : Fin n → ℝ) (e : E), coeffs.γ s x e = 0)
    (x₀ : Fin n → ℝ) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (W : MultidimBrownianMotion P d) (X : ℝ → Ω → Fin n → ℝ),
      (∀ k, IsBrownianFiltration (W.W k) (usualFiltration W)) ∧
      (usualFiltration W).IsRightContinuous ∧
      Measurable (Function.uncurry X) ∧
      (∀ i, Probability.ProgressivelyMeasurable (usualFiltration W) fun ω s => X s ω i) ∧
      (∀ᵐ ω ∂P, X 0 ω = x₀) ∧
      (∀ᵐ ω ∂P, ContinuousOn (fun t => X t ω) (Set.Ici 0)) ∧
      (∀ T : ℝ, 0 < T →
        ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T,
          ∑ i, (‖X (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤) ∧
      (∀ T, SolvesOn W (zeroPoisson P) (usualFiltration W)
        (usualFiltration_brownian W) (zeroPoisson_isPoissonFiltration P (usualFiltration W))
        coeffs x₀ X T) := by
  obtain ⟨Ω, _, P, _, ⟨W⟩⟩ := MultidimBrownianMotion.exists.{0} d
  obtain ⟨X, hX⟩ := exists_continuous_globalDiffusion W (usualFiltration W)
    (usualFiltration_brownian W) (usualFiltration_beforeZero W) (usualFiltration_null W)
    coeffs hReg hLip hγ x₀
  exact ⟨Ω, inferInstance, P, inferInstance, W, X, usualFiltration_brownian W,
    inferInstance, hX⟩

#print axioms exists_constructed_continuous_globalDiffusion
end KLSLevyProbe

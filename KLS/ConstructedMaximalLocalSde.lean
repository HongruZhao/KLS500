import KLS.LocalFamilyEquation
import KLS.LocalFamilyExitIdentification

/-! Actual construction of a maximal local SDE, with the lifetime left explicit. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology
noncomputable section
namespace KLS.LocalDiffusion
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
open KLSLevyProbe
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {N d : ℕ} {W : MultidimBrownianMotion P d} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ}
  {b : (Fin N → ℝ) → Fin N → ℝ} {s : Fin d → (Fin N → ℝ) → Fin N → ℝ}

/-- Certificates proved for the actual assembled path and its genuine exit times.
A finite lifetime is allowed, and entails escape from every bounded state ball. -/
def IsMaximalLocalSde (D : LocalProcessFamily W ℱ hW b s) : Prop :=
  IsStoppingTime ℱ D.lifetime ∧
  (∀ᵐ ω ∂P, (0 : WithTop ℝ) < D.lifetime ω) ∧
  Measurable (Function.uncurry fun ω t => D.path t ω) ∧
  (∀ i : Fin N, Probability.ProgressivelyMeasurable ℱ (fun ω t => D.path t ω i)) ∧
  (D.path 0 =ᵐ[P] 0) ∧
  (∀ᵐ ω ∂P, ContinuousOn (fun t => D.path t ω)
    {t : ℝ | 0 ≤ t ∧ (t : WithTop ℝ) < D.lifetime ω}) ∧
  (∀ᵐ ω ∂P, ∀ m : ℕ,
    D.exit m ω = Probability.exitTime (fun ω t => D.path t ω) ((m : ℝ)+1) ω) ∧
  (∀ᵐ ω ∂P, D.lifetime ω ≠ ⊤ → ∀ B : ℝ,
    ∃ t : ℝ, 0 ≤ t ∧ (t : WithTop ℝ) < D.lifetime ω ∧ B ≤ ‖D.path t ω‖) ∧
  (∀ m : ℕ, ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂P, (T : WithTop ℝ) ≤ D.exit m ω → ∀ i : Fin N,
    D.path T ω i = (∫ t in Icc (0 : ℝ) T, b (D.path t ω) i ∂volume) +
      ∑ k : Fin d, D.noiseIntegral m i k T ω)

theorem LocalProcessFamily.isMaximalLocalSde (D : LocalProcessFamily W ℱ hW b s) :
    IsMaximalLocalSde D :=
  ⟨D.lifetime_isStoppingTime, D.lifetime_pos, D.measurable_path, D.progressive_path,
    D.path_initial, D.ae_continuousOn_before_lifetime, D.ae_exit_eq_path,
    D.ae_finite_lifetime_escape, fun m T hT => D.originalEquation m hT⟩

/-- Brownian existence, genuine Lipschitz-extension Picard solutions, proved
compatibility, and countable assembly produce the maximal local process. -/
theorem exists_constructed_maximalLocalSde
    (b : (Fin N → ℝ) → Fin N → ℝ) (s : Fin d → (Fin N → ℝ) → Fin N → ℝ)
    (hb : LocallyLipschitz b) (hs : ∀ k, LocallyLipschitz (s k)) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (W : MultidimBrownianMotion P d)
      (D : LocalProcessFamily W (usualFiltration W) (usualFiltration_brownian W) b s),
      IsMaximalLocalSde D := by
  obtain ⟨Ω, mΩ, P, hP, W, hD⟩ := exists_constructed_localProcesses b s hb hs
  let D : LocalProcessFamily W (usualFiltration W) (usualFiltration_brownian W) b s :=
    fun m => Classical.choice (hD ((m : ℝ)+1) (by positivity))
  exact ⟨Ω, mΩ, P, hP, W, D, D.isMaximalLocalSde⟩

end KLS.LocalDiffusion
end
#print axioms KLS.LocalDiffusion.exists_constructed_maximalLocalSde

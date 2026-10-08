import KLS.ConstructedGlobalDiffusion
import LevyStochCalc.Probability.ExitTime
import LevyStochCalc.Probability.StoppedProgressive

/-!
An actual Picard diffusion and its everywhere-continuous vector-Itô representative.
The representative supplies genuine norm-exit stopping times. Coefficients in the
Itô representation remain evaluated along the Picard process; the two paths agree
on one event of probability one for all nonnegative times.
-/
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
namespace KLSLevyAdapter
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
open LevyStochCalc.Brownian.Ito LevyStochCalc.Ito.Setting LevyStochCalc.Ito.Picard
open KLSLevyProbe

universe u v
variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {n d : ℕ}

structure GlobalDiffusionPair (W : MultidimBrownianMotion P d)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hW : ∀ k, IsBrownianFiltration (W.W k) ℱ)
    (coeffs : JumpDiffusionCoeffs n d E) (x₀ : Fin n → ℝ) where
  X : ℝ → Ω → Fin n → ℝ
  measurable_X : Measurable (Function.uncurry X)
  progressive_X : ∀ i, Probability.ProgressivelyMeasurable ℱ fun ω s => X s ω i
  initial_X : ∀ᵐ ω ∂P, X 0 ω = x₀
  sup_X : ∀ T : ℝ, 0 < T →
    ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T, ∑ i, (‖X (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤
  solves_X : ∀ T, SolvesOn W (zeroPoisson.{u,v,0} P) ℱ hW
    (zeroPoisson_isPoissonFiltration.{u,v,0} P ℱ) coeffs x₀ X T
  Y : ℝ → Ω → Fin n → ℝ
  ito_Y : DiffusionRepresentation W (zeroPoisson.{u,v,0} P) ℱ hW
    (zeroPoisson_isPoissonFiltration.{u,v,0} P ℱ) coeffs x₀ X solves_X Y
  path_eq : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → X t ω = Y t ω

/-- The paired process is built by Picard existence; a solution is not a premise. -/
theorem nonempty_globalDiffusionPair
    (W : MultidimBrownianMotion P d) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    [ℱ.IsRightContinuous] (hW : ∀ k, IsBrownianFiltration (W.W k) ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (coeffs : JumpDiffusionCoeffs n d E)
    (hReg : JumpDiffusionCoeffs.IsRegular coeffs (0 : Measure E))
    {L : ℝ} (hLip : JumpDiffusionCoeffs.IsLipschitz coeffs (0 : Measure E) L)
    (hγ : ∀ s x e, coeffs.γ s x e = 0) (x₀ : Fin n → ℝ) :
    Nonempty (GlobalDiffusionPair W ℱ hW coeffs x₀) := by
  obtain ⟨X, hXm, hXa, hX0, hXcad, hXS, hsol⟩ :=
    exists_globalSolution W (zeroPoisson.{u,v,0} P) ℱ hW
      (zeroPoisson_isPoissonFiltration.{u,v,0} P ℱ) coeffs hℱ0 hnull hReg hLip x₀
  have hRight : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      Tendsto (fun s => X s ω) (nhdsWithin t (Set.Ioi t)) (𝓝 (X t ω)) :=
    hXcad.mono fun _ h t ht => (h t ht).1
  obtain ⟨Y, hY, hXY, _⟩ := exists_continuousVersion_of_zeroJump W (zeroPoisson.{u,v,0} P) ℱ
    hW (zeroPoisson_isPoissonFiltration.{u,v,0} P ℱ) coeffs x₀ X hsol hℱ0 hnull hReg hLip hγ
    hXm hXa hRight hXS
  exact ⟨⟨X, hXm, hXa, hX0, hXS, hsol, Y, hY, hXY⟩⟩

/-- Brownian existence supplies the probability space, driver and common filtration. -/
theorem exists_constructed_globalDiffusionPair
    {E : Type} [MeasurableSpace E] (coeffs : JumpDiffusionCoeffs n d E)
    (hReg : JumpDiffusionCoeffs.IsRegular coeffs (0 : Measure E))
    {L : ℝ} (hLip : JumpDiffusionCoeffs.IsLipschitz coeffs (0 : Measure E) L)
    (hγ : ∀ s x e, coeffs.γ s x e = 0) (x₀ : Fin n → ℝ) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (W : MultidimBrownianMotion P d),
      Nonempty (GlobalDiffusionPair W (usualFiltration W) (usualFiltration_brownian W) coeffs x₀) := by
  obtain ⟨Ω, _, P, _, ⟨W⟩⟩ := MultidimBrownianMotion.exists.{0} d
  exact ⟨Ω, inferInstance, P, inferInstance, W,
    nonempty_globalDiffusionPair W (usualFiltration W) (usualFiltration_brownian W)
      (usualFiltration_beforeZero W) (usualFiltration_null W) coeffs hReg hLip hγ x₀⟩

namespace GlobalDiffusionPair
variable {W : MultidimBrownianMotion P d} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ} {coeffs : JumpDiffusionCoeffs n d E}
  {x₀ : Fin n → ℝ} (D : GlobalDiffusionPair W ℱ hW coeffs x₀)

noncomputable def exit (r : ℝ) : Ω → WithTop ℝ :=
  Probability.exitTime (fun ω t => D.Y t ω) r

theorem exit_isStoppingTime (r : ℝ) : IsStoppingTime ℱ (D.exit r) :=
  Probability.isStoppingTime_exitTime (fun t => (D.ito_Y.adapted t).measurable)
    D.ito_Y.continuous_path r

theorem exit_nonneg (r : ℝ) (ω : Ω) : (0 : WithTop ℝ) ≤ D.exit r ω :=
  Probability.coe_zero_le_exitTime (fun ω t => D.Y t ω) r ω

theorem exit_mono (ω : Ω) : Monotone (fun r => D.exit r ω) :=
  fun _ _ h => Probability.exitTime_mono (fun ω t => D.Y t ω) ω h

/-- Every fixed finite horizon is eventually below the actual norm-exit times, pathwise. -/
theorem exit_covers_horizon (ω : Ω) {T : ℝ} (hT : 0 ≤ T) :
    ∃ R : ℕ, ∀ r : ℕ, R ≤ r → (T : WithTop ℝ) < D.exit (r : ℝ) ω :=
  Probability.exists_lt_exitTime (D.ito_Y.continuous_path ω) hT

theorem norm_le_before_exit (ω : Ω) {r t : ℝ} (ht : 0 < t)
    (hle : (t : WithTop ℝ) ≤ D.exit r ω) : ‖D.Y t ω‖ ≤ r :=
  Probability.norm_le_of_le_exitTime (D.ito_Y.continuous_path ω) ht hle

theorem stopped_diffusion_measurable (r : ℝ) (i : Fin n) (k : Fin d) :
    Measurable (Function.uncurry (Probability.stopped (D.exit r)
      (fun ω s => coeffs.σ s (D.X s ω) i k))) :=
  Probability.measurable_uncurry_stopped (D.exit_isStoppingTime r) ((D.solves_X 0).h_σ_meas i k)

theorem stopped_diffusion_progressive (r : ℝ) (i : Fin n) (k : Fin d) :
    Probability.ProgressivelyMeasurable ℱ (Probability.stopped (D.exit r)
      (fun ω s => coeffs.σ s (D.X s ω) i k)) :=
  Probability.ProgressivelyMeasurable.stopped (D.exit_isStoppingTime r)
    ((D.solves_X 0).h_σ_progMeas i k)

/-- The stopped coefficients have finite energy from the actual solution's certificates. -/
theorem stopped_diffusion_energy (r : ℝ) (i : Fin n) (k : Fin d) (T : ℝ) (hT : 0 < T) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖Probability.stopped (D.exit r) (fun ω s => coeffs.σ s (D.X s ω) i k) ω s‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P < ⊤ := by
  refine lt_of_le_of_lt (lintegral_mono fun ω => lintegral_mono fun s => ?_)
    ((D.solves_X 0).h_σ_sq i k T hT)
  unfold Probability.stopped
  split_ifs <;> simp

end GlobalDiffusionPair
#print axioms nonempty_globalDiffusionPair
#print axioms exists_constructed_globalDiffusionPair
#print axioms GlobalDiffusionPair.exit_isStoppingTime
#print axioms GlobalDiffusionPair.exit_covers_horizon
#print axioms GlobalDiffusionPair.stopped_diffusion_energy
end KLSLevyAdapter

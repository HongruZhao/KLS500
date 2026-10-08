import KLS.LocalCoefficientExtension
import KLS.StoppedDiffusionIntegral

/-! Actual local diffusions constructed from Lipschitz extensions on state balls.
No compatibility between radii, maximal solution, or nonexplosion is asserted. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology
noncomputable section
namespace KLS.LocalDiffusion
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
open LevyStochCalc.Brownian.Ito LevyStochCalc.Ito.Setting
open KLSLevyAdapter KLSLevyProbe
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {N d : ℕ}

/-- A constructed global extension together with exact agreement with the original
coefficients on the stated ball. The local stochastic equation is proved below. -/
structure LocalProcess (W : MultidimBrownianMotion P d)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hW : ∀ k, IsBrownianFiltration (W.W k) ℱ)
    (b : (Fin N → ℝ) → Fin N → ℝ) (s : Fin d → (Fin N → ℝ) → Fin N → ℝ) (R : ℝ) where
  radius_nonneg : 0 ≤ R
  drift_continuous : Continuous b
  diffusion_continuous : ∀ k, Continuous (s k)
  extension : JumpDiffusionCoeffs N d Unit
  regular : extension.IsRegular (0 : Measure Unit)
  lipschitz : ∃ L : ℝ, extension.IsLipschitz (0 : Measure Unit) L
  drift_eq : ∀ t x, ‖x‖ ≤ R → extension.μ t x = b x
  diffusion_eq : ∀ t x, ‖x‖ ≤ R → ∀ i k, extension.σ t x i k = s k x i
  zero_jump : ∀ t x e, extension.γ t x e = 0
  pair : GlobalDiffusionPair W ℱ hW extension 0

theorem nonempty_localProcess
    (W : MultidimBrownianMotion P d) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    [ℱ.IsRightContinuous] (hW : ∀ k, IsBrownianFiltration (W.W k) ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[ℱ 0] A)
    (b : (Fin N → ℝ) → Fin N → ℝ) (s : Fin d → (Fin N → ℝ) → Fin N → ℝ)
    (hb : LocallyLipschitz b) (hs : ∀ k, LocallyLipschitz (s k))
    (R : ℝ) (hR : 0 ≤ R) : Nonempty (LocalProcess W ℱ hW b s R) := by
  obtain ⟨C, hreg, ⟨L, hlip⟩, hbC, hsC, hz⟩ := exists_extension_on_closedBall b s hb hs R
  obtain ⟨D⟩ := nonempty_globalDiffusionPair W ℱ hW hℱ0 hnull C hreg hlip hz 0
  exact ⟨⟨hR, hb.continuous, fun k => (hs k).continuous,
    C, hreg, ⟨L, hlip⟩, hbC, hsC, hz, D⟩⟩

/-- All ball-local constructions use one actually constructed Brownian driver.
This does not yet assert agreement of different ball-local processes. -/
theorem exists_constructed_localProcesses
    (b : (Fin N → ℝ) → Fin N → ℝ) (s : Fin d → (Fin N → ℝ) → Fin N → ℝ)
    (hb : LocallyLipschitz b) (hs : ∀ k, LocallyLipschitz (s k)) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (W : MultidimBrownianMotion P d), ∀ R : ℝ, 0 < R →
      Nonempty (LocalProcess W (usualFiltration W) (usualFiltration_brownian W) b s R) := by
  obtain ⟨Ω, _, P, _, ⟨W⟩⟩ := MultidimBrownianMotion.exists.{0} d
  exact ⟨Ω, inferInstance, P, inferInstance, W, fun R hR =>
    nonempty_localProcess W (usualFiltration W) (usualFiltration_brownian W)
      (usualFiltration_beforeZero W) (usualFiltration_null W) b s hb hs R hR.le⟩

namespace LocalProcess
variable {W : MultidimBrownianMotion P d} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ}
  {b : (Fin N → ℝ) → Fin N → ℝ} {s : Fin d → (Fin N → ℝ) → Fin N → ℝ} {R : ℝ}
  (D : LocalProcess W ℱ hW b s R)

def exit : Ω → WithTop ℝ := D.pair.exit R

theorem exit_isStoppingTime : IsStoppingTime ℱ D.exit := D.pair.exit_isStoppingTime R

theorem initial_Y : ∀ᵐ ω ∂P, D.pair.Y 0 ω = 0 := by
  filter_upwards [D.pair.initial_X, D.pair.path_eq] with ω h0 heq
  rw [← heq 0 le_rfl]
  exact h0

theorem exit_pos (hR : 0 < R) : ∀ᵐ ω ∂P, (0 : WithTop ℝ) < D.exit ω := by
  filter_upwards [D.initial_Y] with ω h0
  apply lt_of_not_ge
  intro hle
  obtain ⟨t, ht, hn⟩ := (Probability.exitTime_le_iff (D.pair.ito_Y.continuous_path ω) R 0).mp hle
  have ht0 : t = 0 := le_antisymm ht.2 ht.1
  rw [ht0, h0, norm_zero] at hn
  exact hR.not_ge hn

theorem norm_le_before_exit (ω : Ω) (h0 : D.pair.Y 0 ω = 0) {t : ℝ}
    (ht : 0 ≤ t) (hte : (t : WithTop ℝ) ≤ D.exit ω) : ‖D.pair.Y t ω‖ ≤ R := by
  rcases ht.eq_or_lt with h | h
  · rw [← h, h0, norm_zero]
    exact D.radius_nonneg
  · exact D.pair.norm_le_before_exit ω h hte

theorem original_coefficients_before_exit :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) ≤ D.exit ω →
      D.extension.μ t (D.pair.X t ω) = b (D.pair.Y t ω) ∧
      ∀ i k, D.extension.σ t (D.pair.X t ω) i k = s k (D.pair.Y t ω) i := by
  filter_upwards [D.initial_Y, D.pair.path_eq] with ω h0 heq t ht hte
  rw [heq t ht]
  have hn := D.norm_le_before_exit ω h0 ht hte
  exact ⟨D.drift_eq t _ hn, D.diffusion_eq t _ hn⟩

def noise (i : Fin N) (k : Fin d) : Ω → ℝ → ℝ :=
  Probability.stopped D.exit (fun ω t => s k (D.pair.Y t ω) i)

theorem noise_measurable (i : Fin N) (k : Fin d) :
    Measurable (Function.uncurry (D.noise i k)) :=
  Probability.measurable_uncurry_stopped D.exit_isStoppingTime
    (D.pair.ito_Y.measurable_uncurry_comp
      (((continuous_apply i).comp (D.diffusion_continuous k)).measurable))

theorem noise_progressive (i : Fin N) (k : Fin d) :
    Probability.ProgressivelyMeasurable ℱ (D.noise i k) :=
  Probability.ProgressivelyMeasurable.stopped D.exit_isStoppingTime
    (D.pair.ito_Y.progressivelyMeasurable_comp
      ((continuous_apply i).comp (D.diffusion_continuous k)))

theorem noise_eq_stopped_extension (i : Fin N) (k : Fin d) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → D.noise i k ω t =
      Probability.stopped (D.pair.exit R) (fun ω t => D.extension.σ t (D.pair.X t ω) i k) ω t := by
  filter_upwards [D.original_coefficients_before_exit] with ω hω t ht
  unfold noise Probability.stopped
  change (if (t : WithTop ℝ) ≤ D.exit ω then s k (D.pair.Y t ω) i else 0) =
    (if (t : WithTop ℝ) ≤ D.exit ω then D.extension.σ t (D.pair.X t ω) i k else 0)
  by_cases hte : (t : WithTop ℝ) ≤ D.exit ω
  · rw [if_pos hte, if_pos hte]
    exact ((hω t ht hte).2 i k).symm
  · rw [if_neg hte, if_neg hte]

theorem noise_energy (i : Fin N) (k : Fin d) (T : ℝ) (hT : 0 < T) :
    ∫⁻ ω, ∫⁻ t in Set.Icc (0 : ℝ) T,
      (‖D.noise i k ω t‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  have heq : (∫⁻ ω, ∫⁻ t in Set.Icc (0 : ℝ) T,
      (‖D.noise i k ω t‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P) =
      ∫⁻ ω, ∫⁻ t in Set.Icc (0 : ℝ) T,
        (‖Probability.stopped (D.pair.exit R)
          (fun ω t => D.extension.σ t (D.pair.X t ω) i k) ω t‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
    apply lintegral_congr_ae
    filter_upwards [D.noise_eq_stopped_extension i k] with ω hω
    exact setLIntegral_congr_fun measurableSet_Icc fun t ht => by rw [hω t ht.1]
  rw [heq]
  exact D.pair.stopped_diffusion_energy R i k T hT

end LocalProcess
end KLS.LocalDiffusion
end
#print axioms KLS.LocalDiffusion.exists_constructed_localProcesses
#print axioms KLS.LocalDiffusion.LocalProcess.exit_pos
#print axioms KLS.LocalDiffusion.LocalProcess.noise_energy

import KLS.LocalFamilyRegularity

/-! The assembled process satisfies the literal original-coefficient local SDE. -/
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

def noise (m : ℕ) (i : Fin N) (k : Fin d) : Ω → ℝ → ℝ :=
  Probability.stopped (D.exit m) (fun ω t => s k (D.path t ω) i)

theorem noise_measurable (m : ℕ) (i : Fin N) (k : Fin d) :
    Measurable (Function.uncurry (D.noise m i k)) :=
  Probability.measurable_uncurry_stopped (D.exit_isStoppingTime m)
    ((((continuous_apply i).comp ((D m).diffusion_continuous k)).measurable).comp D.measurable_path)

theorem noise_progressive (m : ℕ) (i : Fin N) (k : Fin d) :
    Probability.ProgressivelyMeasurable ℱ (D.noise m i k) :=
  Probability.ProgressivelyMeasurable.stopped (D.exit_isStoppingTime m)
    (progressivelyMeasurable_comp_state (f := fun _ x => s k x i) D.progressive_path
      ((((continuous_apply i).comp ((D m).diffusion_continuous k)).measurable).comp measurable_snd))

theorem noise_eq_local (m : ℕ) (i : Fin N) (k : Fin d) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → D.noise m i k ω t = (D m).noise i k ω t := by
  filter_upwards [D.ae_path_eq_of_le_exit] with ω hp t ht
  unfold noise LocalProcess.noise Probability.stopped
  change (if (t : WithTop ℝ) ≤ D.exit m ω then s k (D.path t ω) i else 0) =
    (if (t : WithTop ℝ) ≤ D.exit m ω then s k ((D m).pair.Y t ω) i else 0)
  by_cases he : (t : WithTop ℝ) ≤ D.exit m ω
  · rw [if_pos he, if_pos he, hp m t ht he]
  · rw [if_neg he, if_neg he]

theorem noise_energy (m : ℕ) (i : Fin N) (k : Fin d) (T : ℝ) (hT : 0 < T) :
    ∫⁻ ω, ∫⁻ t in Icc (0 : ℝ) T,
      (‖D.noise m i k ω t‖₊ : ℝ≥0∞)^2 ∂volume ∂P < ⊤ := by
  have heq : (∫⁻ ω, ∫⁻ t in Icc (0 : ℝ) T,
      (‖D.noise m i k ω t‖₊ : ℝ≥0∞)^2 ∂volume ∂P) =
      ∫⁻ ω, ∫⁻ t in Icc (0 : ℝ) T,
        (‖(D m).noise i k ω t‖₊ : ℝ≥0∞)^2 ∂volume ∂P := by
    apply lintegral_congr_ae
    filter_upwards [D.noise_eq_local m i k] with ω hω
    exact setLIntegral_congr_fun measurableSet_Icc fun t ht => by rw [hω t ht.1]
  rw [heq]
  exact (D m).noise_energy i k T hT

def noiseIntegral (m : ℕ) (i : Fin N) (k : Fin d) (T : ℝ) : Ω → ℝ :=
  stochasticIntegralBrownian (W.W k) ℱ (hW k) (D.noise m i k)
    (D.noise_measurable m i k) (D.noise_progressive m i k) (D.noise_energy m i k) T

theorem noiseIntegral_eq_local (m : ℕ) (i : Fin N) (k : Fin d) {T : ℝ} (hT : 0 < T) :
    D.noiseIntegral m i k T =ᵐ[P] (D m).noiseIntegral i k T :=
  stochasticIntegral_congr_ae_nonneg (W.W k) ℱ (hW k)
    (D.noise_measurable m i k) ((D m).noise_measurable i k)
    (D.noise_progressive m i k) ((D m).noise_progressive i k)
    (D.noise_energy m i k) ((D m).noise_energy i k) (D.noise_eq_local m i k) hT

/-- The original drift is evaluated along the assembled path and the Brownian
integrands are literally its original diffusion, stopped at the genuine exits. -/
theorem originalEquation (m : ℕ) {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, (T : WithTop ℝ) ≤ D.exit m ω → ∀ i : Fin N,
      D.path T ω i = (∫ t in Icc (0 : ℝ) T, b (D.path t ω) i ∂volume) +
        ∑ k : Fin d, D.noiseIntegral m i k T ω := by
  have hn : ∀ᵐ ω ∂P, ∀ i : Fin N, ∀ k : Fin d,
      D.noiseIntegral m i k T ω = (D m).noiseIntegral i k T ω :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun k => D.noiseIntegral_eq_local m i k hT
  filter_upwards [D.ae_path_eq_of_le_exit, (D m).originalEquation hT, hn]
    with ω hp he hn hle i
  rw [hp m T hT.le hle, he hle i]
  congr 1
  · apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    have htm : (t : WithTop ℝ) ≤ D.exit m ω :=
      (show (t : WithTop ℝ) ≤ (T : WithTop ℝ) by exact_mod_cast ht.2).trans hle
    change b ((D m).pair.Y t ω) i = b (D.path t ω) i
    rw [hp m t ht.1 htm]
  · exact Finset.sum_congr rfl fun k _ => (hn i k).symm

end KLS.LocalDiffusion.LocalProcessFamily
end
#print axioms KLS.LocalDiffusion.LocalProcessFamily.noise_energy
#print axioms KLS.LocalDiffusion.LocalProcessFamily.originalEquation

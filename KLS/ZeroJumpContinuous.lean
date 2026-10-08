import KLS.ContinuousProcessVersion
import LevyStochCalc.Ito.PicardGlobal
import LevyStochCalc.Ito.VectorItoVersionLimit
import LevyStochCalc.Poisson.CompensatedPullOut

/-!
Consumer joining genuine Picard existence to continuous vector-Itô versions.
Acceptance status and source hashes are recorded separately in the replay receipts.

The intended application starts with Picard.exists_globalSolution. Its concrete
outputs discharge hXm, hXa, hRight, hSup and hsol below. IsRegular + IsLipschitz
discharge the drift admissibility rather than leaving it as an extra premise.
The zero jump term is removed by a proved compensated-integral vanishing lemma.

The resulting Y is an everywhere continuous adapted vector-Itô version with
coefficients evaluated along X, and X and Y are indistinguishable for t≥0.
We do not silently identify arbitrary representatives or switch an uncountable
family of per-time almost-sure equalities with one pathwise almost-sure identity.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace KLSLevyProbe

open LevyStochCalc
open LevyStochCalc.Brownian
open LevyStochCalc.Brownian.Multidim
open LevyStochCalc.Brownian.Ito
open LevyStochCalc.Ito.Setting
open LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {n d : ℕ}

variable (W : MultidimBrownianMotion P d) (N : Poisson.PoissonRandomMeasure P ν)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hW : ∀ k, IsBrownianFiltration (W.W k) ℱ)
  (hN : Poisson.IsPoissonFiltration N ℱ)
  (coeffs : JumpDiffusionCoeffs n d E) (x₀ : Fin n → ℝ)
  (X : ℝ → Ω → Fin n → ℝ)
  (hsol : ∀ T, SolvesOn W N ℱ hW hN coeffs x₀ X T)

abbrev DiffusionRepresentation (Y : ℝ → Ω → Fin n → ℝ) : Prop :=
  IsVectorItoVersion W ℱ hW (fun i k ω s => coeffs.σ s (X s ω) i k)
    (hsol 0).h_σ_meas (hsol 0).h_σ_progMeas (hsol 0).h_σ_sq
    (fun _ => x₀) (fun i ω s => coeffs.μ s (X s ω) i) Y

theorem zeroJump_ae_vectorItoProcess
    (hγ : ∀ (s : ℝ) (x : Fin n → ℝ) (e : E), coeffs.γ s x e = 0)
    {t : ℝ} (ht : 0 ≤ t) :
    X t =ᵐ[P] vectorItoProcess W ℱ hW (fun i k ω s => coeffs.σ s (X s ω) i k)
      (hsol 0).h_σ_meas (hsol 0).h_σ_progMeas (hsol 0).h_σ_sq
      (fun _ => x₀) (fun i ω s => coeffs.μ s (X s ω) i) t := by
  have hJ : ∀ᵐ ω ∂P, ∀ i : Fin n,
      picardStep_jump N ℱ hN coeffs X
        (hsol 0).h_γ_meas (hsol 0).h_γ_progMeas (hsol 0).h_γ_sq t ω i = 0 := by
    refine ae_all_iff.mpr fun i => ?_
    exact Poisson.Compensated.stochasticIntegral_ae_zero_of_vanishing N hN
      (fun ω s e => coeffs.γ s (X s ω) e i)
      ((hsol 0).h_γ_meas i) ((hsol 0).h_γ_progMeas i) ((hsol 0).h_γ_sq i) ht
      (fun ω s e _ => by simp [hγ])
  filter_upwards [(hsol t).eqn t ⟨ht, le_rfl⟩, hJ] with ω hω hJω
  funext i
  rw [hω i]
  simp only [picardStep, Pi.add_apply, hJω i, add_zero, picardStep_drift,
    vectorItoProcess, vectorItoMartingale, coordItoIntegral, picardStep_diffusion,
    MultidimBrownianMotion.stochasticIntegral, Brownian.Ito.stochasticIntegral]

theorem exists_continuousVersion_of_zeroJump
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (hReg : JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (hγ : ∀ (s : ℝ) (x : Fin n → ℝ) (e : E), coeffs.γ s x e = 0)
    (hXm : Measurable (Function.uncurry X))
    (hXa : ∀ i, Probability.ProgressivelyMeasurable ℱ fun ω s => X s ω i)
    (hRight : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      Tendsto (fun s => X s ω) (nhdsWithin t (Set.Ioi t)) (𝓝 (X t ω)))
    (hSup : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T, ∑ i, (‖X (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤) :
    ∃ Y : ℝ → Ω → Fin n → ℝ,
      DiffusionRepresentation W N ℱ hW hN coeffs x₀ X hsol Y ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → X t ω = Y t ω) ∧
      (∀ᵐ ω ∂P, ContinuousOn (fun t => X t ω) (Set.Ici 0)) := by
  have hbm : ∀ i : Fin n, Measurable
      (Function.uncurry fun ω s => coeffs.μ s (X s ω) i) := by
    intro i
    exact ((measurable_pi_apply i).comp hReg.1).comp
      (measurable_snd.prodMk (hXm.comp measurable_swap))
  have hbp : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ
      (fun ω s => coeffs.μ s (X s ω) i) := fun i =>
    progressivelyMeasurable_comp_state (f := fun s x => coeffs.μ s x i) hXa
      ((measurable_pi_apply i).comp hReg.1)
  have hbq : ∀ (i : Fin n) (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    fun i _ hT => lintegral_sq_mu_lt_top_of_energy coeffs hReg hLip
      (lintegral_lintegral_sq_lt_top_of_supL2 hSup) i hT
  obtain ⟨Y, hY⟩ := exists_isVectorItoVersion_of_unbounded W ℱ hW
    (fun i k ω s => coeffs.σ s (X s ω) i k)
    (hsol 0).h_σ_meas (hsol 0).h_σ_progMeas (hsol 0).h_σ_sq
    hℱ0 hnull (X₀ := fun _ => x₀) (fun _ => measurable_const)
    (fun i ω s => coeffs.μ s (X s ω) i) hbm hbp hbq
  have hmod : ∀ t : ℝ, 0 ≤ t → X t =ᵐ[P] Y t := fun t ht =>
    (zeroJump_ae_vectorItoProcess W N ℱ hW hN coeffs x₀ X hsol hγ ht).trans
      (hY.ae_eq t ht).symm
  have hboth := KLS.ae_continuousOn_nonneg_of_continuous_version hRight hY.continuous_path hmod
  exact ⟨Y, hY, hboth.mono (fun _ h => h.2), hboth.mono (fun _ h => h.1)⟩

#print axioms zeroJump_ae_vectorItoProcess
#print axioms exists_continuousVersion_of_zeroJump

end KLSLevyProbe

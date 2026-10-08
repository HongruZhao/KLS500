import KLS.AdaptiveLogMGFBounds

/-! Genuine unstopped log-MGF Brownian integrals with proved finite energy. -/
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS.AdaptiveLocalization
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
open LevyStochCalc.Brownian.Ito LevyStochCalc.Ito.Picard KLS.LocalDiffusion KLSLevyProbe
universe u
variable {n : ℕ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {μ : Measure (Space n)} [IsProbabilityMeasure μ]
  {W : MultidimBrownianMotion P n} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ}
namespace MaximalProcess
variable (D : MaximalProcess μ W ℱ hW) (w : Space n)

def globalLogMGFNoise (k : Fin n) : Ω → ℝ → ℝ :=
  fun ω t => logMGFNoiseCoefficient μ w k (D.path t ω)

theorem globalLogMGFNoise_measurable (hμ : IsCompact μ.support) (k : Fin n) :
    Measurable (Function.uncurry (D.globalLogMGFNoise w k)) :=
  (((contDiff_coordinateLogMGFGradient hμ w).continuous.clm_apply
    ((D 0).diffusion_continuous k)).measurable).comp D.measurable_path

theorem globalLogMGFNoise_progressive (hμ : IsCompact μ.support) (k : Fin n) :
    Probability.ProgressivelyMeasurable ℱ (D.globalLogMGFNoise w k) :=
  progressivelyMeasurable_comp_state (f := fun _ z => logMGFNoiseCoefficient μ w k z)
    D.progressive_path ((((contDiff_coordinateLogMGFGradient hμ w).continuous.clm_apply
      ((D 0).diffusion_continuous k)).measurable).comp measurable_snd)

theorem ae_all_globalLogMGFNoise_bound (hμ : IsCompact μ.support) (hadm : admissibleMeasure μ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[ℱ 0] A) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ k : Fin n,
      |D.globalLogMGFNoise w k ω t| ≤ logMGFUniformNoiseBound hμ w := by
  filter_upwards [D.ae_all_localizationLaw_logConcave_global hμ hadm hℱ0 hnull] with ω hlc t ht k
  exact abs_logMGFNoiseCoefficient_le hμ hadm.isotropic.affineSpan_support_eq_top w
    (D.path t ω) (hlc t ht) k

theorem globalLogMGFNoise_energy_bound (hμ : IsCompact μ.support) (hadm : admissibleMeasure μ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[ℱ 0] A)
    (k : Fin n) (T : ℝ) :
    (∫⁻ ω, ∫⁻ t in Icc (0 : ℝ) T,
      (‖D.globalLogMGFNoise w k ω t‖₊ : ℝ≥0∞)^2 ∂volume ∂P) ≤
      (ENNReal.ofReal (logMGFUniformNoiseBound hμ w))^2 * ENNReal.ofReal T := by
  calc
    _ ≤ ∫⁻ _ω, ∫⁻ _t in Icc (0 : ℝ) T,
        (ENNReal.ofReal (logMGFUniformNoiseBound hμ w))^2 ∂volume ∂P := by
      apply lintegral_mono_ae
      filter_upwards [D.ae_all_globalLogMGFNoise_bound w hμ hadm hℱ0 hnull] with ω hω
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      apply pow_le_pow_left'
      rw [← ENNReal.ofReal_coe_nnreal]
      simpa only [coe_nnnorm, Real.norm_eq_abs] using ENNReal.ofReal_le_ofReal (hω t ht.1 k)
    _ = _ := by simp [Real.volume_Icc]

theorem globalLogMGFNoise_energy (hμ : IsCompact μ.support) (hadm : admissibleMeasure μ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[ℱ 0] A)
    (k : Fin n) (T : ℝ) (_hT : 0 < T) :
    (∫⁻ ω, ∫⁻ t in Icc (0 : ℝ) T,
      (‖D.globalLogMGFNoise w k ω t‖₊ : ℝ≥0∞)^2 ∂volume ∂P) < ⊤ :=
  (D.globalLogMGFNoise_energy_bound w hμ hadm hℱ0 hnull k T).trans_lt
    (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) ENNReal.ofReal_lt_top)

def globalLogMGFNoiseIntegral (hμ : IsCompact μ.support) (hadm : admissibleMeasure μ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[ℱ 0] A)
    (k : Fin n) (T : ℝ) : Ω → ℝ :=
  stochasticIntegralBrownian (W.W k) ℱ (hW k) (D.globalLogMGFNoise w k)
    (D.globalLogMGFNoise_measurable w hμ k) (D.globalLogMGFNoise_progressive w hμ k)
    (D.globalLogMGFNoise_energy w hμ hadm hℱ0 hnull k) T

theorem globalLogMGFNoiseIntegral_martingale (hμ : IsCompact μ.support) (hadm : admissibleMeasure μ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[ℱ 0] A) (k : Fin n) :
    Martingale (D.globalLogMGFNoiseIntegral w hμ hadm hℱ0 hnull k) ℱ P :=
  martingale_stochasticIntegralBrownian (W.W k) ℱ (hW k) (D.globalLogMGFNoise w k)
    (D.globalLogMGFNoise_measurable w hμ k) (D.globalLogMGFNoise_progressive w hμ k)
    (D.globalLogMGFNoise_energy w hμ hadm hℱ0 hnull k)

end MaximalProcess
end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.MaximalProcess.globalLogMGFNoiseIntegral_martingale

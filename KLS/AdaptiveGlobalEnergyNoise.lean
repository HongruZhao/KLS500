import KLS.AdaptiveEnergyNoiseBound

/-! Genuine unstopped Brownian energy integrals with finite L2 energy. -/
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped NNReal ENNReal Topology BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS.AdaptiveLocalization
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
open LevyStochCalc.Brownian.Ito LevyStochCalc.Ito.Picard KLS.LocalDiffusion KLSLevyProbe
universe v
variable {n : ℕ} {Ω : Type v} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {μ : Measure (Space n)} [IsProbabilityMeasure μ]
  {W : MultidimBrownianMotion P n} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ}
namespace MaximalProcess
variable (D : MaximalProcess μ W ℱ hW)

def globalEnergyNoise (r : ℕ) (u : Space n) (k : Fin n) : Ω → ℝ → ℝ :=
  fun ω t => energyNoiseCoefficient μ r u k (D.path t ω)

theorem globalEnergyNoise_measurable (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (r : ℕ) (u : Space n) (k : Fin n) :
    Measurable (Function.uncurry (D.globalEnergyNoise r u k)) :=
  ((((contDiff_cumulantEnergy hμ hfull u).continuous_fderiv (by simp)).clm_apply
    ((D 0).diffusion_continuous k)).measurable).comp D.measurable_path

theorem globalEnergyNoise_progressive (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (r : ℕ) (u : Space n) (k : Fin n) :
    Probability.ProgressivelyMeasurable ℱ (D.globalEnergyNoise r u k) :=
  progressivelyMeasurable_comp_state (f := fun _ z => energyNoiseCoefficient μ r u k z)
    D.progressive_path (((((contDiff_cumulantEnergy hμ hfull u).continuous_fderiv
      (by simp)).clm_apply ((D 0).diffusion_continuous k)).measurable).comp measurable_snd)

theorem ae_all_globalEnergyNoise_bound (hμ : IsCompact μ.support) (hadm : admissibleMeasure μ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[ℱ 0] A)
    (r : ℕ) (hr : 1 ≤ r) (u : Space n) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ k : Fin n,
      |D.globalEnergyNoise r u k ω t| ≤ energyUniformNoiseBound hμ r u := by
  filter_upwards [D.ae_all_localizationLaw_logConcave_global hμ hadm hℱ0 hnull] with ω hlc t ht k
  exact abs_energyNoiseCoefficient_le hμ hadm.isotropic.affineSpan_support_eq_top hr u k
    (D.path t ω) (hlc t ht)

theorem globalEnergyNoise_energy_bound (hμ : IsCompact μ.support) (hadm : admissibleMeasure μ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[ℱ 0] A)
    (r : ℕ) (hr : 1 ≤ r) (u : Space n) (k : Fin n) (T : ℝ) :
    (∫⁻ ω, ∫⁻ t in Icc (0 : ℝ) T, (‖D.globalEnergyNoise r u k ω t‖₊ : ℝ≥0∞)^2 ∂volume ∂P) ≤
      (ENNReal.ofReal (energyUniformNoiseBound hμ r u))^2 * ENNReal.ofReal T := by
  calc
    _ ≤ ∫⁻ _ω, ∫⁻ _t in Icc (0 : ℝ) T,
        (ENNReal.ofReal (energyUniformNoiseBound hμ r u))^2 ∂volume ∂P := by
      apply lintegral_mono_ae
      filter_upwards [D.ae_all_globalEnergyNoise_bound hμ hadm hℱ0 hnull r hr u] with ω hω
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      apply pow_le_pow_left'
      rw [← ENNReal.ofReal_coe_nnreal]
      simpa only [coe_nnnorm, Real.norm_eq_abs] using ENNReal.ofReal_le_ofReal (hω t ht.1 k)
    _ = _ := by simp [Real.volume_Icc]

theorem globalEnergyNoise_energy (hμ : IsCompact μ.support) (hadm : admissibleMeasure μ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[ℱ 0] A)
    (r : ℕ) (hr : 1 ≤ r) (u : Space n) (k : Fin n) (T : ℝ) (_hT : 0 < T) :
    (∫⁻ ω, ∫⁻ t in Icc (0 : ℝ) T, (‖D.globalEnergyNoise r u k ω t‖₊ : ℝ≥0∞)^2 ∂volume ∂P) < ⊤ :=
  (D.globalEnergyNoise_energy_bound hμ hadm hℱ0 hnull r hr u k T).trans_lt
    (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) ENNReal.ofReal_lt_top)

def globalEnergyNoiseIntegral (hμ : IsCompact μ.support) (hadm : admissibleMeasure μ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[ℱ 0] A)
    (r : ℕ) (hr : 1 ≤ r) (u : Space n) (k : Fin n) (T : ℝ) : Ω → ℝ :=
  stochasticIntegralBrownian (W.W k) ℱ (hW k) (D.globalEnergyNoise r u k)
    (D.globalEnergyNoise_measurable hμ hadm.isotropic.affineSpan_support_eq_top r u k)
    (D.globalEnergyNoise_progressive hμ hadm.isotropic.affineSpan_support_eq_top r u k)
    (D.globalEnergyNoise_energy hμ hadm hℱ0 hnull r hr u k) T

theorem globalEnergyNoiseIntegral_martingale (hμ : IsCompact μ.support) (hadm : admissibleMeasure μ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[ℱ 0] A)
    (r : ℕ) (hr : 1 ≤ r) (u : Space n) (k : Fin n) :
    Martingale (D.globalEnergyNoiseIntegral hμ hadm hℱ0 hnull r hr u k) ℱ P :=
  martingale_stochasticIntegralBrownian (W.W k) ℱ (hW k) (D.globalEnergyNoise r u k)
    (D.globalEnergyNoise_measurable hμ hadm.isotropic.affineSpan_support_eq_top r u k)
    (D.globalEnergyNoise_progressive hμ hadm.isotropic.affineSpan_support_eq_top r u k)
    (D.globalEnergyNoise_energy hμ hadm hℱ0 hnull r hr u k)

theorem integral_globalEnergyNoiseIntegral_eq_zero (hμ : IsCompact μ.support) (hadm : admissibleMeasure μ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[ℱ 0] A)
    (r : ℕ) (hr : 1 ≤ r) (u : Space n) (k : Fin n) {T : ℝ} (hT : 0 ≤ T) :
    (∫ ω, D.globalEnergyNoiseIntegral hμ hadm hℱ0 hnull r hr u k T ω ∂P) = 0 := by
  have hm := D.globalEnergyNoiseIntegral_martingale hμ hadm hℱ0 hnull r hr u k
  have hz := stochasticIntegralBrownian_ae_zero_of_nonpos (W.W k) ℱ (hW k)
    (D.globalEnergyNoise r u k)
    (D.globalEnergyNoise_measurable hμ hadm.isotropic.affineSpan_support_eq_top r u k)
    (D.globalEnergyNoise_progressive hμ hadm.isotropic.affineSpan_support_eq_top r u k)
    (D.globalEnergyNoise_energy hμ hadm hℱ0 hnull r hr u k) (show (0 : ℝ) ≤ 0 from le_rfl)
  have he : (∫ ω, D.globalEnergyNoiseIntegral hμ hadm hℱ0 hnull r hr u k 0 ω ∂P) =
      ∫ ω, D.globalEnergyNoiseIntegral hμ hadm hℱ0 hnull r hr u k T ω ∂P := by
    simpa only [setIntegral_univ] using hm.setIntegral_eq hT (s := Set.univ) MeasurableSet.univ
  rw [← he]
  exact (integral_congr_ae hz).trans (by simp)

end MaximalProcess
end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.MaximalProcess.globalEnergyNoiseIntegral_martingale
#print axioms KLS.AdaptiveLocalization.MaximalProcess.integral_globalEnergyNoiseIntegral_eq_zero

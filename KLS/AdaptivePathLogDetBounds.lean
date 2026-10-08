import KLS.AdaptiveLogDetBounds

/-! Uniform logdet drift/noise bounds on the actual process and its stopped Brownian integrals. -/
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped NNReal ENNReal Topology BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
namespace KLS.AdaptiveLocalization
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
open LevyStochCalc.Brownian.Ito KLS.LocalDiffusion KLSLevyProbe
universe u
variable {n : ℕ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {μ : Measure (Space n)} [IsProbabilityMeasure μ]
  {W : MultidimBrownianMotion P n} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ}
namespace MaximalProcess
variable (D : MaximalProcess μ W ℱ hW)

/-- All nonnegative times before lifetime share the same event and dimension-only constants. -/
theorem ae_all_logDet_bounds (hμ : IsCompact μ.support) (hadm : admissibleMeasure μ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) < D.lifetime ω →
      (∀ k : Fin n, |logDetNoiseCoefficient μ k (D.path t ω)| ≤
        (n : ℝ)*normalizedThirdMomentBound n) ∧
      (0 ≤ logDetTraceCorrection μ (D.path t ω)) ∧
      (logDetTraceCorrection μ (D.path t ω) ≤ (n : ℝ)^3*(normalizedThirdMomentBound n)^2) ∧
      (logDetNoiseSquared μ (D.path t ω) ≤ (n : ℝ)^3*(normalizedThirdMomentBound n)^2) := by
  filter_upwards [D.ae_all_localizationLaw_logConcave hμ hadm] with ω hlc t ht hlife
  have hl := hlc t ht hlife
  have hfull := hadm.isotropic.affineSpan_support_eq_top
  exact ⟨fun k => abs_logDetNoiseCoefficient_le hμ hfull _ hl k,
    logDetTraceCorrection_nonneg hμ hfull _, logDetTraceCorrection_le hμ hfull _ hl,
    logDetNoiseSquared_le hμ hfull _ hl⟩

/-- Each actual stopped trace coefficient is uniformly bounded, with one event
for all exits, all nonnegative times, and all Brownian coordinates. -/
theorem ae_all_logDetNoise_abs_le (hμ : IsCompact μ.support) (hadm : admissibleMeasure μ) :
    ∀ᵐ ω ∂P, ∀ m : ℕ, ∀ t : ℝ, 0 ≤ t → ∀ k : Fin n,
      |D.logDetNoise m k ω t| ≤ (n : ℝ)*normalizedThirdMomentBound n := by
  filter_upwards [D.ae_all_logDet_bounds hμ hadm, D.ae_finite_before_next_exit]
    with ω hb hn m t ht k
  unfold logDetNoise Probability.stopped
  change |if (t : WithTop ℝ) ≤ D.exit m ω then _ else 0| ≤ _
  split_ifs with he
  · exact (hb t ht ((hn m t ht he).trans_le (D.exit_le_lifetime (m+1) ω))).1 k
  · simpa using mul_nonneg (Nat.cast_nonneg n) (normalizedThirdMomentBound_pos n).le

theorem logDetNoise_energy_bound (hμ : IsCompact μ.support) (hadm : admissibleMeasure μ)
    (m : ℕ) (k : Fin n) (T : ℝ) :
    (∫⁻ ω, ∫⁻ t in Icc (0 : ℝ) T,
      (‖D.logDetNoise m k ω t‖₊ : ℝ≥0∞)^2 ∂volume ∂P) ≤
      (ENNReal.ofReal ((n : ℝ)*normalizedThirdMomentBound n))^2 * ENNReal.ofReal T := by
  calc
    _ ≤ ∫⁻ _ω, ∫⁻ _t in Icc (0 : ℝ) T,
        (ENNReal.ofReal ((n : ℝ)*normalizedThirdMomentBound n))^2 ∂volume ∂P := by
      apply lintegral_mono_ae
      filter_upwards [D.ae_all_logDetNoise_abs_le hμ hadm] with ω hω
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      apply pow_le_pow_left'
      rw [← ENNReal.ofReal_coe_nnreal]
      simpa only [coe_nnnorm, Real.norm_eq_abs] using
        ENNReal.ofReal_le_ofReal (hω m t ht.1 k)
    _ = _ := by simp [Real.volume_Icc]

/-- A genuine Ito-isometry estimate uniform in the radius index. -/
theorem logDetNoiseIntegral_secondMoment_bound (hμ : IsCompact μ.support)
    (hadm : admissibleMeasure μ) (m : ℕ) (k : Fin n) {T : ℝ} (hT : 0 < T) :
    (∫⁻ ω, (‖D.logDetNoiseIntegral hμ hadm.isotropic.affineSpan_support_eq_top m k T ω‖₊ : ℝ≥0∞)^2 ∂P) ≤
      (ENNReal.ofReal ((n : ℝ)*normalizedThirdMomentBound n))^2 * ENNReal.ofReal T := by
  unfold logDetNoiseIntegral
  rw [isometry_stochasticIntegralBrownian (W.W k) ℱ (hW k) (D.logDetNoise m k)
    (D.logDetNoise_measurable hμ hadm.isotropic.affineSpan_support_eq_top m k)
    (D.logDetNoise_progressive hμ hadm.isotropic.affineSpan_support_eq_top m k)
    (D.logDetNoise_energy hμ hadm.isotropic.affineSpan_support_eq_top m k) hT]
  exact D.logDetNoise_energy_bound hμ hadm m k T

end MaximalProcess
end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.MaximalProcess.ae_all_logDet_bounds
#print axioms KLS.AdaptiveLocalization.MaximalProcess.logDetNoiseIntegral_secondMoment_bound

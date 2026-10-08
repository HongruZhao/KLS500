import KLS.AdaptiveGlobalLogMGFIto

/-! The literal log-MGF drift is integrable on every finite Brownian-time product interval. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
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
variable (D : MaximalProcess μ W ℱ hW) (w : Space n)

theorem logMGFDrift_path_measurable (hμ : IsCompact μ.support) :
    Measurable (Function.uncurry fun ω t => logMGFDrift μ w (D.path t ω)) := by
  have hn (k : Fin n) : Continuous (logMGFNoiseCoefficient μ w k) :=
    (contDiff_coordinateLogMGFGradient hμ w).continuous.clm_apply ((D 0).diffusion_continuous k)
  have hd : Continuous (logMGFDrift μ w) :=
    continuous_const.mul (continuous_finsetSum _ fun k _ => (hn k).pow 2)
  exact hd.measurable.comp D.measurable_path

theorem logMGFDrift_path_integrable_prod (hμ : IsCompact μ.support) (hadm : admissibleMeasure μ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[ℱ 0] A) (T : ℝ) :
    Integrable (Function.uncurry fun ω t => logMGFDrift μ w (D.path t ω))
      (P.prod (volume.restrict (Icc (0 : ℝ) T))) := by
  have hm := D.logMGFDrift_path_measurable w hμ
  apply Integrable.of_bound hm.aestronglyMeasurable ((1/2)*(n : ℝ)*(logMGFUniformNoiseBound hμ w)^2)
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_le hm.norm measurable_const)).mpr
  filter_upwards [D.ae_all_localizationLaw_logConcave_global hμ hadm hℱ0 hnull] with ω hlc
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact abs_logMGFDrift_le hμ hadm.isotropic.affineSpan_support_eq_top w (D.path t ω) (hlc t ht.1)

/-- The finite variation integral in (71) is a genuine finite Bochner integral almost surely. -/
theorem ae_integrableOn_logMGFDrift (hμ : IsCompact μ.support) (hadm : admissibleMeasure μ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[ℱ 0] A) (T : ℝ) :
    ∀ᵐ ω ∂P, IntegrableOn (fun t => logMGFDrift μ w (D.path t ω)) (Icc (0 : ℝ) T) volume :=
  (D.logMGFDrift_path_integrable_prod w hμ hadm hℱ0 hnull T).prod_right_ae

end MaximalProcess
end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.MaximalProcess.logMGFDrift_path_integrable_prod
#print axioms KLS.AdaptiveLocalization.MaximalProcess.ae_integrableOn_logMGFDrift

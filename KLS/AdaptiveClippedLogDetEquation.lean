import KLS.AdaptiveClippedLogDet

/-! The actual logdet equation agrees with globally bounded clipped coefficients before exits. -/
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

theorem logDetNoise_eq_stopped_clipped (hμ : IsCompact μ.support)
    (hadm : admissibleMeasure μ) (m : ℕ) (k : Fin n) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → D.logDetNoise m k ω t =
      Probability.stopped (D.exit m) (D.clippedLogDetNoise k) ω t := by
  filter_upwards [D.ae_all_clippedLogDet_eq hμ hadm, D.ae_finite_before_next_exit]
    with ω hc hn t ht
  unfold logDetNoise Probability.stopped
  change (if (t : WithTop ℝ) ≤ D.exit m ω then _ else 0) =
    (if (t : WithTop ℝ) ≤ D.exit m ω then _ else 0)
  split_ifs with he
  · exact ((hc t ht ((hn m t ht he).trans_le (D.exit_le_lifetime (m+1) ω))).1 k).symm
  · rfl

theorem logDetNoiseIntegral_eq_clipped (hμ : IsCompact μ.support)
    (hadm : admissibleMeasure μ) (m : ℕ) (k : Fin n) {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, (T : WithTop ℝ) ≤ D.exit m ω →
      D.logDetNoiseIntegral hμ hadm.isotropic.affineSpan_support_eq_top m k T ω =
      D.clippedLogDetNoiseIntegral hμ hadm.isotropic.affineSpan_support_eq_top k T ω := by
  have hfull := hadm.isotropic.affineSpan_support_eq_top
  have hm := D.clippedLogDetNoise_measurable hμ hfull k
  have hp := D.clippedLogDetNoise_progressive hμ hfull k
  have hq := D.clippedLogDetNoise_energy k
  have hms := Probability.measurable_uncurry_stopped (D.exit_isStoppingTime m) hm
  have hps := hp.stopped (D.exit_isStoppingTime m)
  have hqs := energy_lt_top_of_abs_le
    (fun ω t => Probability.abs_stopped_le (D.exit m) (D.clippedLogDetNoise k) ω t) hq
  have hi := stochasticIntegral_congr_ae_nonneg (W.W k) ℱ (hW k)
    (D.logDetNoise_measurable hμ hfull m k) hms
    (D.logDetNoise_progressive hμ hfull m k) hps
    (D.logDetNoise_energy hμ hfull m k) hqs
    (D.logDetNoise_eq_stopped_clipped hμ hadm m k) hT
  have hs := stochasticIntegralBrownian_stopped_eq_of_le (D.exit m) (W.W k) ℱ (hW k)
    (D.exit_isStoppingTime m) hm hp hq hT
  filter_upwards [hi, hs] with ω hiω hsω hle
  exact hiω.trans (hsω hle)

theorem clippedLogDet_equation (hμ : IsCompact μ.support) (hadm : admissibleMeasure μ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[ℱ 0] A)
    (m : ℕ) {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, (T : WithTop ℝ) ≤ D.exit m ω →
      Real.log (D.covariancePath T ω).det - Real.log (covariance μ 0 0).det =
        (∫ t in Icc (0 : ℝ) T, D.clippedLogDetDrift ω t ∂volume) +
          ∑ k : Fin n, D.clippedLogDetNoiseIntegral hμ hadm.isotropic.affineSpan_support_eq_top k T ω := by
  have hn : ∀ᵐ ω ∂P, ∀ k : Fin n, (T : WithTop ℝ) ≤ D.exit m ω →
      D.logDetNoiseIntegral hμ hadm.isotropic.affineSpan_support_eq_top m k T ω =
      D.clippedLogDetNoiseIntegral hμ hadm.isotropic.affineSpan_support_eq_top k T ω :=
    ae_all_iff.mpr fun k => D.logDetNoiseIntegral_eq_clipped hμ hadm m k hT
  filter_upwards [D.logDet_equation hμ hadm.isotropic.affineSpan_support_eq_top hℱ0 hnull m hT,
    D.ae_all_clippedLogDet_eq hμ hadm, D.ae_finite_before_next_exit, hn]
    with ω he hc hx hnoise hle
  have hd : (∫ t in Icc (0 : ℝ) T,
      -(n : ℝ) - 1/2 * logDetTraceCorrection μ (D.path t ω) ∂volume) =
      ∫ t in Icc (0 : ℝ) T, D.clippedLogDetDrift ω t ∂volume := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    have hte : (t : WithTop ℝ) ≤ D.exit m ω :=
      (show (t : WithTop ℝ) ≤ (T : WithTop ℝ) by exact_mod_cast ht.2).trans hle
    exact (hc t ht.1 ((hx m t ht.1 hte).trans_le (D.exit_le_lifetime (m+1) ω))).2.symm
  exact (he hle).trans (congrArg₂ (fun x y : ℝ => x+y) hd
    (Finset.sum_congr rfl fun k _ => hnoise k hle))

end MaximalProcess
end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.MaximalProcess.clippedLogDet_equation

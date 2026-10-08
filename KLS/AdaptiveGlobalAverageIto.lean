import KLS.AdaptiveLocalAverageIto

/-! Equation (68) for each measurable test function bounded on the compact base support. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology Matrix.Norms.Elementwise
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
variable (D : MaximalProcess μ W ℱ hW) (f : Space n → ℝ)
variable (hμ : IsCompact μ.support) (hadm : admissibleMeasure μ)
    (hf : Measurable f) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ x ∈ μ.support, |f x| ≤ B)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[ℱ 0] A)

omit hμ hadm hf hB0 hB hℱ0 hnull in
theorem localAverageNoise_eq_stopped_global (m : ℕ) (k : Fin n) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → BallProcess.averageNoise f (D m) k ω t =
      Probability.stopped (D.exit m) (D.globalAverageNoise f k) ω t := by
  filter_upwards [D.ae_path_eq_of_le_exit] with ω hp t ht
  unfold BallProcess.averageNoise globalAverageNoise Probability.stopped
  change (if (t : WithTop ℝ) ≤ D.exit m ω then _ else 0) =
    (if (t : WithTop ℝ) ≤ D.exit m ω then _ else 0)
  split_ifs with he
  · dsimp only
    rw [hp m t ht he]
  · rfl

theorem localAverageNoiseIntegral_eq_global (m : ℕ) (k : Fin n) {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, (T : WithTop ℝ) ≤ D.exit m ω →
      BallProcess.averageNoiseIntegral f (D m) hμ (integrable_of_bounded_on_support hf hB) k T ω =
        D.globalAverageNoiseIntegral f hμ hadm hf hB0 hB hℱ0 hnull k T ω := by
  have hfi := integrable_of_bounded_on_support hf hB
  have hm := D.globalAverageNoise_measurable f hμ hfi k
  have hp := D.globalAverageNoise_progressive f hμ hfi k
  have hq := D.globalAverageNoise_energy f hμ hadm hf hB0 hB hℱ0 hnull k
  have hms := Probability.measurable_uncurry_stopped (D.exit_isStoppingTime m) hm
  have hps := hp.stopped (D.exit_isStoppingTime m)
  have hqs := energy_lt_top_of_abs_le
    (fun ω t => Probability.abs_stopped_le (D.exit m) (D.globalAverageNoise f k) ω t) hq
  have ha := BallProcess.averageNoise_admissible f (D m) hμ hfi k
  have hi := stochasticIntegral_congr_ae_nonneg (W.W k) ℱ (hW k)
    ha.1 hms ha.2.1 hps ha.2.2 hqs (D.localAverageNoise_eq_stopped_global f m k) hT
  have hs := stochasticIntegralBrownian_stopped_eq_of_le (D.exit m) (W.W k) ℱ (hW k)
    (D.exit_isStoppingTime m) hm hp hq hT
  filter_upwards [hi, hs] with ω hiω hsω hle
  exact hiω.trans (hsω hle)

/-- The law is the actual normalized exponential tilt of the constructed global
adaptive process. Both sides use the literal integrals of the test function. -/
theorem average_equation_global {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, (∫ x, f x ∂D.localizationLaw T ω) - (∫ x, f x ∂μ) =
      ∑ k : Fin n, D.globalAverageNoiseIntegral f hμ hadm hf hB0 hB hℱ0 hnull k T ω := by
  have hfi := integrable_of_bounded_on_support hf hB
  have he := ae_all_iff.mpr fun m : ℕ =>
    BallProcess.average_equation f (D m) hμ hadm.isotropic.affineSpan_support_eq_top hfi hℱ0 hnull hT
  have hn := ae_all_iff.mpr fun m : ℕ => ae_all_iff.mpr fun k : Fin n =>
    D.localAverageNoiseIntegral_eq_global f hμ hadm hf hB0 hB hℱ0 hnull m k hT
  filter_upwards [he, hn, D.ae_lifetime_eq_top hμ hadm hℱ0 hnull, D.ae_path_eq_of_le_exit]
    with ω heω hnω htop hp
  obtain ⟨m, hm⟩ := (D.lt_lifetime_iff ω T).mp (by rw [htop]; exact WithTop.coe_lt_top T)
  have h := heω m hm.le
  rw [← hp m T hT.le hm.le] at h
  exact h.trans (Finset.sum_congr rfl fun k _ => hnω m k hm.le)

include hμ hf hB in
/-- Identification of the integrand in (68), including the actual principal
inverse-square-root covariance normalization. -/
theorem globalAverageNoise_eq_integral (k : Fin n) (ω : Ω) (t : ℝ) :
    D.globalAverageNoise f k ω t = ∫ x,
      f x * normalizedCenteredVector (D.localizationLaw t ω) x k ∂D.localizationLaw t ω :=
  averageNoiseCoefficient_eq_integral hμ (integrable_of_bounded_on_support hf hB) _ _

theorem integral_globalAverageNoiseIntegral_eq_zero (k : Fin n) {T : ℝ} (hT : 0 ≤ T) :
    (∫ ω, D.globalAverageNoiseIntegral f hμ hadm hf hB0 hB hℱ0 hnull k T ω ∂P) = 0 := by
  have hm := D.globalAverageNoiseIntegral_martingale f hμ hadm hf hB0 hB hℱ0 hnull k
  have hz := stochasticIntegralBrownian_ae_zero_of_nonpos (W.W k) ℱ (hW k)
    (D.globalAverageNoise f k) (D.globalAverageNoise_measurable f hμ (integrable_of_bounded_on_support hf hB) k)
    (D.globalAverageNoise_progressive f hμ (integrable_of_bounded_on_support hf hB) k)
    (D.globalAverageNoise_energy f hμ hadm hf hB0 hB hℱ0 hnull k) (show (0 : ℝ) ≤ 0 from le_rfl)
  have he : (∫ ω, D.globalAverageNoiseIntegral f hμ hadm hf hB0 hB hℱ0 hnull k 0 ω ∂P) =
      ∫ ω, D.globalAverageNoiseIntegral f hμ hadm hf hB0 hB hℱ0 hnull k T ω ∂P := by
    simpa only [setIntegral_univ] using hm.setIntegral_eq hT (s := Set.univ) MeasurableSet.univ
  rw [← he]
  exact (integral_congr_ae hz).trans (by simp)

end MaximalProcess
end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.MaximalProcess.average_equation_global
#print axioms KLS.AdaptiveLocalization.MaximalProcess.globalAverageNoise_eq_integral

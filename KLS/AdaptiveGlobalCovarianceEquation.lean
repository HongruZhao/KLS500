import KLS.AdaptiveGlobalCovarianceNoise

/-! The actual covariance equation holds at every finite deterministic horizon without stopping. -/
open MeasureTheory ProbabilityTheory Set Filter Matrix
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
variable (D : MaximalProcess μ W ℱ hW)
variable (hμ : IsCompact μ.support) (hadm : admissibleMeasure μ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[ℱ 0] A)

theorem covarianceNoiseIntegral_eq_global (m : ℕ) (i j k : Fin n) {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, (T : WithTop ℝ) ≤ D.exit m ω →
      D.covarianceNoiseIntegral hμ m i j k T ω =
        D.globalCovarianceNoiseIntegral hμ hadm hℱ0 hnull i j k T ω :=
  stochasticIntegralBrownian_stopped_eq_of_le (D.exit m) (W.W k) ℱ (hW k)
    (D.exit_isStoppingTime m) (D.globalCovarianceNoise_measurable hμ i j k)
    (D.globalCovarianceNoise_progressive hμ i j k) (D.globalCovarianceNoise_energy hμ hadm hℱ0 hnull i j k) hT

theorem covariance_equation_global (i j : Fin n) {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, D.covariancePath T ω i j - covariance μ 0 0 i j =
      -(∫ t in Icc (0 : ℝ) T, D.covariancePath t ω i j ∂volume) +
        ∑ k : Fin n, D.globalCovarianceNoiseIntegral hμ hadm hℱ0 hnull i j k T ω := by
  have he := ae_all_iff.mpr fun m : ℕ =>
    D.covariance_equation hμ hadm.isotropic.affineSpan_support_eq_top hℱ0 hnull m i j hT
  have hn := ae_all_iff.mpr fun m : ℕ => ae_all_iff.mpr fun k : Fin n =>
    D.covarianceNoiseIntegral_eq_global hμ hadm hℱ0 hnull m i j k hT
  filter_upwards [he, hn, D.ae_lifetime_eq_top hμ hadm hℱ0 hnull] with ω heω hnω htop
  obtain ⟨m, hm⟩ := (D.lt_lifetime_iff ω T).mp (by rw [htop]; exact WithTop.coe_lt_top T)
  exact (heω m hm.le).trans (congrArg (fun a : ℝ =>
    -(∫ t in Icc (0 : ℝ) T, D.covariancePath t ω i j ∂volume) + a)
      (Finset.sum_congr rfl fun k _ => hnω m k hm.le))

theorem integral_globalCovarianceNoiseIntegral_eq_zero (i j k : Fin n) {T : ℝ} (hT : 0 ≤ T) :
    (∫ ω, D.globalCovarianceNoiseIntegral hμ hadm hℱ0 hnull i j k T ω ∂P) = 0 := by
  have hm := D.globalCovarianceNoiseIntegral_martingale hμ hadm hℱ0 hnull i j k
  have hz := stochasticIntegralBrownian_ae_zero_of_nonpos (W.W k) ℱ (hW k)
    (D.globalCovarianceNoise i j k) (D.globalCovarianceNoise_measurable hμ i j k)
    (D.globalCovarianceNoise_progressive hμ i j k)
    (D.globalCovarianceNoise_energy hμ hadm hℱ0 hnull i j k) (show (0 : ℝ) ≤ 0 from le_rfl)
  have he : (∫ ω, D.globalCovarianceNoiseIntegral hμ hadm hℱ0 hnull i j k 0 ω ∂P) =
      ∫ ω, D.globalCovarianceNoiseIntegral hμ hadm hℱ0 hnull i j k T ω ∂P := by
    simpa only [setIntegral_univ] using hm.setIntegral_eq hT (s := Set.univ) MeasurableSet.univ
  rw [← he]
  exact (integral_congr_ae hz).trans (by simp)

end MaximalProcess
end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.MaximalProcess.covariance_equation_global
#print axioms KLS.AdaptiveLocalization.MaximalProcess.integral_globalCovarianceNoiseIntegral_eq_zero

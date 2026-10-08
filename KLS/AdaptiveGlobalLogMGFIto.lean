import KLS.AdaptiveLocalLogMGFIto

/-! The genuine global log-MGF stochastic equation (71) for the constructed adaptive process. -/
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
variable (D : MaximalProcess μ W ℱ hW) (w : Space n)

def logMGFPath (t : ℝ) (ω : Ω) : ℝ := tiltLogLaplace (D.localizationLaw t ω) w

omit [IsProbabilityMeasure μ] in
theorem localLogMGFNoise_eq_stopped_global (m : ℕ) (k : Fin n) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → BallProcess.logMGFNoise w (D m) k ω t =
      Probability.stopped (D.exit m) (D.globalLogMGFNoise w k) ω t := by
  filter_upwards [D.ae_path_eq_of_le_exit] with ω hp t ht
  unfold BallProcess.logMGFNoise globalLogMGFNoise Probability.stopped
  change (if (t : WithTop ℝ) ≤ D.exit m ω then _ else 0) =
    (if (t : WithTop ℝ) ≤ D.exit m ω then _ else 0)
  split_ifs with he
  · dsimp only
    rw [hp m t ht he]
  · rfl

variable (hμ : IsCompact μ.support) (hadm : admissibleMeasure μ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[ℱ 0] A)

theorem localLogMGFNoiseIntegral_eq_global (m : ℕ) (k : Fin n) {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, (T : WithTop ℝ) ≤ D.exit m ω →
      BallProcess.logMGFNoiseIntegral w (D m) hμ k T ω =
        D.globalLogMGFNoiseIntegral w hμ hadm hℱ0 hnull k T ω := by
  have hm := D.globalLogMGFNoise_measurable w hμ k
  have hp := D.globalLogMGFNoise_progressive w hμ k
  have hq := D.globalLogMGFNoise_energy w hμ hadm hℱ0 hnull k
  have hms := Probability.measurable_uncurry_stopped (D.exit_isStoppingTime m) hm
  have hps := hp.stopped (D.exit_isStoppingTime m)
  have hqs := energy_lt_top_of_abs_le
    (fun ω t => Probability.abs_stopped_le (D.exit m) (D.globalLogMGFNoise w k) ω t) hq
  have ha := BallProcess.logMGFNoise_admissible w (D m) hμ k
  have hi := stochasticIntegral_congr_ae_nonneg (W.W k) ℱ (hW k)
    ha.1 hms ha.2.1 hps ha.2.2 hqs (D.localLogMGFNoise_eq_stopped_global w m k) hT
  have hs := stochasticIntegralBrownian_stopped_eq_of_le (D.exit m) (W.W k) ℱ (hW k)
    (D.exit_isStoppingTime m) hm hp hq hT
  filter_upwards [hi, hs] with ω hiω hsω hle
  exact hiω.trans (hsω hle)

/-- Actual fixed-spatial-vector log-MGF dynamics at each deterministic positive horizon. -/
theorem logMGF_equation_global {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, D.logMGFPath w T ω - tiltLogLaplace μ w =
      (∫ t in Icc (0 : ℝ) T, logMGFDrift μ w (D.path t ω) ∂volume) +
        ∑ k : Fin n, D.globalLogMGFNoiseIntegral w hμ hadm hℱ0 hnull k T ω := by
  have he := ae_all_iff.mpr fun m : ℕ =>
    BallProcess.logMGF_equation w (D m) hμ hadm.isotropic.affineSpan_support_eq_top hℱ0 hnull hT
  have hn := ae_all_iff.mpr fun m : ℕ => ae_all_iff.mpr fun k : Fin n =>
    D.localLogMGFNoiseIntegral_eq_global w hμ hadm hℱ0 hnull m k hT
  filter_upwards [he, hn, D.ae_lifetime_eq_top hμ hadm hℱ0 hnull, D.ae_path_eq_of_le_exit]
    with ω heω hnω htop hp
  obtain ⟨m, hm⟩ := (D.lt_lifetime_iff ω T).mp (by rw [htop]; exact WithTop.coe_lt_top T)
  have h := heω m hm.le
  rw [← hp m T hT.le hm.le] at h
  have hd : (∫ t in Icc (0 : ℝ) T, logMGFDrift μ w ((D m).pair.Y t ω) ∂volume) =
      ∫ t in Icc (0 : ℝ) T, logMGFDrift μ w (D.path t ω) ∂volume := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    dsimp only
    rw [hp m t ht.1 ((show (t : WithTop ℝ) ≤ (T : WithTop ℝ) by exact_mod_cast ht.2).trans hm.le)]
  exact h.trans (congrArg₂ (fun a b : ℝ => a+b) hd (Finset.sum_congr rfl fun k _ => hnω m k hm.le))

include hμ in
/-- The Brownian integrand is exactly A^{-1/2}(gradient Lambda-a). -/
theorem globalLogMGFNoise_eq_spatial (k : Fin n) (ω : Ω) (t : ℝ) :
    D.globalLogMGFNoise w k ω t = spatialLogMGFNoise μ w (D.path t ω) k :=
  logMGFNoiseCoefficient_eq_spatial hμ w k _

/-- Equation (71), with the actual log-Laplace transform and Euclidean gradient. -/
theorem logMGF_equation_spatial {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, tiltLogLaplace (D.localizationLaw T ω) w - tiltLogLaplace μ w =
      -(1/2) * (∫ t in Icc (0 : ℝ) T, ‖spatialLogMGFNoise μ w (D.path t ω)‖^2 ∂volume) +
        ∑ k : Fin n, D.globalLogMGFNoiseIntegral w hμ hadm hℱ0 hnull k T ω := by
  have he := D.logMGF_equation_global w hμ hadm hℱ0 hnull hT
  have hd (ω : Ω) : (∫ t in Icc (0 : ℝ) T, logMGFDrift μ w (D.path t ω) ∂volume) =
      -(1/2) * (∫ t in Icc (0 : ℝ) T, ‖spatialLogMGFNoise μ w (D.path t ω)‖^2 ∂volume) := by
    simp_rw [logMGFDrift_eq_spatial_norm hμ w]
    exact integral_const_mul _ _
  filter_upwards [he] with ω hω
  exact hω.trans (congrArg (fun a : ℝ => a + _) (hd ω))

end MaximalProcess
end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.MaximalProcess.logMGF_equation_global
#print axioms KLS.AdaptiveLocalization.MaximalProcess.logMGF_equation_spatial

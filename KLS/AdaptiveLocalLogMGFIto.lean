import KLS.AdaptiveGlobalLogMGFNoise
import KLS.LocalSmoothObservableIto

/-! Actual Brownian integrals and local Itô equation for actual log-MGF. -/
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix.Norms.Elementwise
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS.AdaptiveLocalization
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
open LevyStochCalc.Brownian.Ito KLS.LocalDiffusion KLSLevyProbe
universe u
variable {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]
variable (w : Space n)

theorem logMGFNoiseCoefficient_eq_sum (hμ : IsCompact μ.support)
 (k : Fin n) (z : Fin (n+n*n) → ℝ) :
    logMGFNoiseCoefficient μ w k z = ∑ a : Fin (n+n*n),
      coordDeriv (coordinateLogMGFGradient μ w) a z * coordinateDiffusion μ k z a := by
  rw [show logMGFNoiseCoefficient μ w k z = coordinateLogMGFGradient μ w z (coordinateDiffusion μ k z)
    from rfl, apply_eq_sum_coordDeriv]
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {W : MultidimBrownianMotion P n} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ} {R : ℝ}
namespace BallProcess
variable (D : BallProcess μ W ℱ hW R)

def logMGFNoise (k : Fin n) : Ω → ℝ → ℝ :=
  Probability.stopped D.exit (fun ω t => logMGFNoiseCoefficient μ w k (D.pair.Y t ω))

theorem logMGFNoise_eq_sum (hμ : IsCompact μ.support)
 (k : Fin n) : D.logMGFNoise w k =
    fun ω t => ∑ a : Fin (n+n*n), D.observableNoise (coordinateLogMGFGradient μ w) a k ω t := by
  funext ω t
  simp only [logMGFNoise, LocalProcess.observableNoise, LocalProcess.noise, Probability.stopped]
  by_cases ht : (t : WithTop ℝ) ≤ D.exit ω
  · simp only [ht, ite_true, logMGFNoiseCoefficient_eq_sum w hμ]
  · simp only [ht, ite_false, mul_zero, Finset.sum_const_zero]

theorem logMGFNoise_admissible (hμ : IsCompact μ.support)
 (k : Fin n) :
    Measurable (Function.uncurry (D.logMGFNoise w k)) ∧
    Probability.ProgressivelyMeasurable ℱ (D.logMGFNoise w k) ∧
    ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ t in Icc (0 : ℝ) T,
      (‖D.logMGFNoise w k ω t‖₊ : ℝ≥0∞)^2 ∂volume ∂P < ⊤ := by
  have hf := contDiff_coordinateLogMGF hμ w
  obtain ⟨hm, hp, hq, _⟩ := exists_stochasticIntegralBrownian_finsetSum (W.W k) ℱ (hW k)
    (fun a : Fin (n+n*n) => D.observableNoise (coordinateLogMGFGradient μ w) a k)
    (fun a => D.observableNoise_measurable _ (contDiff_coordinateLogMGFGradient hμ w).continuous a k)
    (fun a => D.observableNoise_progressive _ (contDiff_coordinateLogMGFGradient hμ w).continuous a k)
    (fun a => D.smoothObservableNoise_energy (coordinateLogMGF μ w) hf a k)
    Finset.univ (by norm_num : (0 : ℝ) < 1)
  rw [D.logMGFNoise_eq_sum w hμ]
  exact ⟨hm, hp, hq⟩

def logMGFNoiseIntegral (hμ : IsCompact μ.support)
 (k : Fin n) (T : ℝ) : Ω → ℝ :=
  stochasticIntegralBrownian (W.W k) ℱ (hW k) (D.logMGFNoise w k)
    (D.logMGFNoise_admissible w hμ k).1 (D.logMGFNoise_admissible w hμ k).2.1
    (D.logMGFNoise_admissible w hμ k).2.2 T

theorem logMGFNoiseIntegral_eq_sum (hμ : IsCompact μ.support)
 (k : Fin n)
    {T : ℝ} (hT : 0 < T) : D.logMGFNoiseIntegral w hμ k T =ᵐ[P]
      fun ω => ∑ a : Fin (n+n*n), D.smoothObservableNoiseIntegral (coordinateLogMGF μ w)
        (contDiff_coordinateLogMGF hμ w) a k T ω := by
  have hf := contDiff_coordinateLogMGF hμ w
  obtain ⟨hm, hp, hq, he⟩ := exists_stochasticIntegralBrownian_finsetSum (W.W k) ℱ (hW k)
    (fun a : Fin (n+n*n) => D.observableNoise (coordinateLogMGFGradient μ w) a k)
    (fun a => D.observableNoise_measurable _ (contDiff_coordinateLogMGFGradient hμ w).continuous a k)
    (fun a => D.observableNoise_progressive _ (contDiff_coordinateLogMGFGradient hμ w).continuous a k)
    (fun a => D.smoothObservableNoise_energy (coordinateLogMGF μ w) hf a k)
    Finset.univ hT
  unfold logMGFNoiseIntegral
  rw [stochasticIntegralBrownian_congr_fun (W.W k) ℱ (hW k) (D.logMGFNoise_eq_sum w hμ k)
    (D.logMGFNoise_admissible w hμ k).1 (D.logMGFNoise_admissible w hμ k).2.1
    (D.logMGFNoise_admissible w hμ k).2.2 hm hp hq T]
  exact he

/-- The actual log-MGF has its genuine local Itô equation. -/
theorem logMGF_equation (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[ℱ 0] A)
    {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, (T : WithTop ℝ) ≤ D.exit ω →
      coordinateLogMGF μ w (D.pair.Y T ω) - tiltLogLaplace μ w =
        (∫ t in Icc (0 : ℝ) T, logMGFDrift μ w (D.pair.Y t ω) ∂volume) +
          ∑ k : Fin n, D.logMGFNoiseIntegral w hμ k T ω := by
  have hi := D.itoFormula_original_smooth (coordinateLogMGF μ w)
    (contDiff_coordinateLogMGF hμ w) hℱ0 hnull hT
  have hg : observableGenerator (coordinateDrift μ) (coordinateDiffusion μ)
      (coordinateLogMGFGradient μ w) (coordinateLogMGFHessian μ w) = logMGFDrift μ w := by
    funext z
    exact observableGenerator_coordinateLogMGF hμ hfull w z
  have hn : ∀ᵐ ω ∂P, ∀ k : Fin n,
      D.logMGFNoiseIntegral w hμ k T ω =
        ∑ a : Fin (n+n*n), D.smoothObservableNoiseIntegral (coordinateLogMGF μ w)
          (contDiff_coordinateLogMGF hμ w) a k T ω :=
    ae_all_iff.mpr fun k => D.logMGFNoiseIntegral_eq_sum w hμ k hT
  filter_upwards [hi, D.initial_Y, hn] with ω hI h0 hnoise hle
  have h := hI hle
  change coordinateLogMGF μ w (D.pair.Y T ω) - coordinateLogMGF μ w (D.pair.Y 0 ω) =
    (∫ t in Icc (0 : ℝ) T, observableGenerator (coordinateDrift μ) (coordinateDiffusion μ)
      (coordinateLogMGFGradient μ w) (coordinateLogMGFHessian μ w) (D.pair.Y t ω) ∂volume) + _ at h
  rw [hg] at h
  have hs : (∑ a : Fin (n+n*n), ∑ k : Fin n,
      D.smoothObservableNoiseIntegral (coordinateLogMGF μ w) (contDiff_coordinateLogMGF hμ w) a k T ω) =
      ∑ k : Fin n, D.logMGFNoiseIntegral w hμ k T ω := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => (hnoise k).symm
  rw [hs, h0] at h
  have hz : coordinateLogMGF μ w 0 = tiltLogLaplace μ w := by
    rw [coordinateLogMGF_eq_tiltLogLaplace]
    simp only [decodeState_zero, Prod.fst_zero, Prod.snd_zero, law_zero_zero]
  rwa [hz] at h

end BallProcess
end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.BallProcess.logMGF_equation

import KLS.AdaptiveGlobalAverageNoise
import KLS.LocalSmoothObservableIto

/-! Actual Brownian integrals and local Itô equation for actual test averages. -/
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
variable (f : Space n → ℝ)

theorem averageNoiseCoefficient_eq_sum (hμ : IsCompact μ.support)
    (hfi : Integrable f μ) (k : Fin n) (z : Fin (n+n*n) → ℝ) :
    averageNoiseCoefficient μ f k z = ∑ a : Fin (n+n*n),
      coordDeriv (coordinateAverageGradient μ f) a z * coordinateDiffusion μ k z a := by
  rw [show averageNoiseCoefficient μ f k z = coordinateAverageGradient μ f z (coordinateDiffusion μ k z)
    from rfl, apply_eq_sum_coordDeriv]
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {W : MultidimBrownianMotion P n} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ} {R : ℝ}
namespace BallProcess
variable (D : BallProcess μ W ℱ hW R)

def averageNoise (k : Fin n) : Ω → ℝ → ℝ :=
  Probability.stopped D.exit (fun ω t => averageNoiseCoefficient μ f k (D.pair.Y t ω))

theorem averageNoise_eq_sum (hμ : IsCompact μ.support)
    (hfi : Integrable f μ) (k : Fin n) : D.averageNoise f k =
    fun ω t => ∑ a : Fin (n+n*n), D.observableNoise (coordinateAverageGradient μ f) a k ω t := by
  funext ω t
  simp only [averageNoise, LocalProcess.observableNoise, LocalProcess.noise, Probability.stopped]
  by_cases ht : (t : WithTop ℝ) ≤ D.exit ω
  · simp only [ht, ite_true, averageNoiseCoefficient_eq_sum f hμ hfi]
  · simp only [ht, ite_false, mul_zero, Finset.sum_const_zero]

theorem averageNoise_admissible (hμ : IsCompact μ.support)
    (hfi : Integrable f μ) (k : Fin n) :
    Measurable (Function.uncurry (D.averageNoise f k)) ∧
    Probability.ProgressivelyMeasurable ℱ (D.averageNoise f k) ∧
    ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ t in Icc (0 : ℝ) T,
      (‖D.averageNoise f k ω t‖₊ : ℝ≥0∞)^2 ∂volume ∂P < ⊤ := by
  have hf := contDiff_coordinateAverage hμ hfi
  obtain ⟨hm, hp, hq, _⟩ := exists_stochasticIntegralBrownian_finsetSum (W.W k) ℱ (hW k)
    (fun a : Fin (n+n*n) => D.observableNoise (coordinateAverageGradient μ f) a k)
    (fun a => D.observableNoise_measurable _ (contDiff_coordinateAverageGradient hμ hfi).continuous a k)
    (fun a => D.observableNoise_progressive _ (contDiff_coordinateAverageGradient hμ hfi).continuous a k)
    (fun a => D.smoothObservableNoise_energy (coordinateAverage μ f) hf a k)
    Finset.univ (by norm_num : (0 : ℝ) < 1)
  rw [D.averageNoise_eq_sum f hμ hfi]
  exact ⟨hm, hp, hq⟩

def averageNoiseIntegral (hμ : IsCompact μ.support)
    (hfi : Integrable f μ) (k : Fin n) (T : ℝ) : Ω → ℝ :=
  stochasticIntegralBrownian (W.W k) ℱ (hW k) (D.averageNoise f k)
    (D.averageNoise_admissible f hμ hfi k).1 (D.averageNoise_admissible f hμ hfi k).2.1
    (D.averageNoise_admissible f hμ hfi k).2.2 T

theorem averageNoiseIntegral_eq_sum (hμ : IsCompact μ.support)
    (hfi : Integrable f μ) (k : Fin n)
    {T : ℝ} (hT : 0 < T) : D.averageNoiseIntegral f hμ hfi k T =ᵐ[P]
      fun ω => ∑ a : Fin (n+n*n), D.smoothObservableNoiseIntegral (coordinateAverage μ f)
        (contDiff_coordinateAverage hμ hfi) a k T ω := by
  have hf := contDiff_coordinateAverage hμ hfi
  obtain ⟨hm, hp, hq, he⟩ := exists_stochasticIntegralBrownian_finsetSum (W.W k) ℱ (hW k)
    (fun a : Fin (n+n*n) => D.observableNoise (coordinateAverageGradient μ f) a k)
    (fun a => D.observableNoise_measurable _ (contDiff_coordinateAverageGradient hμ hfi).continuous a k)
    (fun a => D.observableNoise_progressive _ (contDiff_coordinateAverageGradient hμ hfi).continuous a k)
    (fun a => D.smoothObservableNoise_energy (coordinateAverage μ f) hf a k)
    Finset.univ hT
  unfold averageNoiseIntegral
  rw [stochasticIntegralBrownian_congr_fun (W.W k) ℱ (hW k) (D.averageNoise_eq_sum f hμ hfi k)
    (D.averageNoise_admissible f hμ hfi k).1 (D.averageNoise_admissible f hμ hfi k).2.1
    (D.averageNoise_admissible f hμ hfi k).2.2 hm hp hq T]
  exact he

/-- The actual law average has no drift before the actual state exit. -/
theorem average_equation (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (hfi : Integrable f μ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[ℱ 0] A)
    {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, (T : WithTop ℝ) ≤ D.exit ω →
      coordinateAverage μ f (D.pair.Y T ω) - (∫ x, f x ∂μ) =
        ∑ k : Fin n, D.averageNoiseIntegral f hμ hfi k T ω := by
  have hi := D.itoFormula_original_smooth (coordinateAverage μ f)
    (contDiff_coordinateAverage hμ hfi) hℱ0 hnull hT
  have hg : observableGenerator (coordinateDrift μ) (coordinateDiffusion μ)
      (coordinateAverageGradient μ f) (coordinateAverageHessian μ f) = fun _ => 0 := by
    funext z
    exact observableGenerator_coordinateAverage hμ hfull hfi z
  have hn : ∀ᵐ ω ∂P, ∀ k : Fin n,
      D.averageNoiseIntegral f hμ hfi k T ω =
        ∑ a : Fin (n+n*n), D.smoothObservableNoiseIntegral (coordinateAverage μ f)
          (contDiff_coordinateAverage hμ hfi) a k T ω :=
    ae_all_iff.mpr fun k => D.averageNoiseIntegral_eq_sum f hμ hfi k hT
  filter_upwards [hi, D.initial_Y, hn] with ω hI h0 hnoise hle
  have h := hI hle
  change coordinateAverage μ f (D.pair.Y T ω) - coordinateAverage μ f (D.pair.Y 0 ω) =
    (∫ t in Icc (0 : ℝ) T, observableGenerator (coordinateDrift μ) (coordinateDiffusion μ)
      (coordinateAverageGradient μ f) (coordinateAverageHessian μ f) (D.pair.Y t ω) ∂volume) + _ at h
  rw [hg, integral_zero, zero_add] at h
  have hs : (∑ a : Fin (n+n*n), ∑ k : Fin n,
      D.smoothObservableNoiseIntegral (coordinateAverage μ f) (contDiff_coordinateAverage hμ hfi) a k T ω) =
      ∑ k : Fin n, D.averageNoiseIntegral f hμ hfi k T ω := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => (hnoise k).symm
  rw [hs, h0] at h
  simpa only [coordinateAverage, decodeState_zero, Prod.fst_zero, Prod.snd_zero, law_zero_zero] using h

end BallProcess
end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.BallProcess.average_equation

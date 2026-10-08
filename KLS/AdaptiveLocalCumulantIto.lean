import KLS.AdaptiveCumulantDrift
import KLS.LocalSmoothObservableIto

/-! Equation (73) for actual cumulants and genuine local Brownian integrals. -/
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
variable (m : ℕ) (h : Fin m → Space n)

def cumulantNoiseCoefficient (μ : Measure (Space n)) (m : ℕ) (h : Fin m → Space n)
    (k : Fin n) (z : Fin (n+n*n) → ℝ) : ℝ :=
  cumulantTensor (law μ (decodeState z).1 (decodeState z).2) (m+1)
    (Fin.cons (inverseSqrtDirection μ z k) h)

theorem contDiff_coordinateCumulantGradient (hμ : IsCompact μ.support) (hm : m ≠ 0) :
    ContDiff ℝ (⊤ : ℕ∞) (coordinateCumulantGradient μ m h) :=
  (contDiff_coordinateCumulant hμ hm h).fderiv_right (by simp)

theorem cumulantNoiseCoefficient_eq_sum (hμ : IsCompact μ.support) (hm : m ≠ 0)
    (k : Fin n) (z : Fin (n+n*n) → ℝ) :
    cumulantNoiseCoefficient μ m h k z = ∑ a : Fin (n+n*n),
      coordDeriv (coordinateCumulantGradient μ m h) a z * coordinateDiffusion μ k z a := by
  rw [show cumulantNoiseCoefficient μ m h k z =
    coordinateCumulantGradient μ m h z (coordinateDiffusion μ k z) from
      (coordinateCumulantGradient_diffusion hμ hm h z k).symm, apply_eq_sum_coordDeriv]
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

theorem observableGenerator_coordinateCumulant (z : Fin (n+n*n) → ℝ) :
    observableGenerator (coordinateDrift μ) (coordinateDiffusion μ)
      (coordinateCumulantGradient μ m h) (coordinateCumulantHessian μ m h) z =
        cumulantGenerator μ m h z := by
  unfold cumulantGenerator
  rw [apply_eq_sum_coordDeriv]
  simp_rw [apply₂_eq_sum_coordDeriv₂]
  unfold observableGenerator
  have hd : (∑ a : Fin (n+n*n), coordDeriv (coordinateCumulantGradient μ m h) a z * coordinateDrift μ z a) =
      ∑ a : Fin (n+n*n), coordinateDrift μ z a * coordDeriv (coordinateCumulantGradient μ m h) a z :=
    Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [hd]
  congr 1
  congr 1
  simp_rw [Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro k _
  ring

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {W : MultidimBrownianMotion P n} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ} {R : ℝ}
namespace BallProcess
variable (D : BallProcess μ W ℱ hW R)

def cumulantNoise (k : Fin n) : Ω → ℝ → ℝ :=
  Probability.stopped D.exit (fun ω t => cumulantNoiseCoefficient μ m h k (D.pair.Y t ω))

theorem cumulantNoise_eq_sum (hμ : IsCompact μ.support) (hm : m ≠ 0)
    (k : Fin n) : D.cumulantNoise m h k =
      fun ω t => ∑ a : Fin (n+n*n), D.observableNoise (coordinateCumulantGradient μ m h) a k ω t := by
  funext ω t
  simp only [cumulantNoise, LocalProcess.observableNoise, LocalProcess.noise, Probability.stopped]
  by_cases ht : (t : WithTop ℝ) ≤ D.exit ω
  · simp only [ht, ite_true, cumulantNoiseCoefficient_eq_sum m h hμ hm]
  · simp only [ht, ite_false, mul_zero, Finset.sum_const_zero]

theorem cumulantNoise_admissible (hμ : IsCompact μ.support) (hm : m ≠ 0)
    (k : Fin n) :
    Measurable (Function.uncurry (D.cumulantNoise m h k)) ∧
    Probability.ProgressivelyMeasurable ℱ (D.cumulantNoise m h k) ∧
    ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ t in Icc (0 : ℝ) T,
      (‖D.cumulantNoise m h k ω t‖₊ : ℝ≥0∞)^2 ∂volume ∂P < ⊤ := by
  have hf := contDiff_coordinateCumulant hμ hm h
  obtain ⟨hm', hp, hq, _⟩ := exists_stochasticIntegralBrownian_finsetSum (W.W k) ℱ (hW k)
    (fun a : Fin (n+n*n) => D.observableNoise (coordinateCumulantGradient μ m h) a k)
    (fun a => D.observableNoise_measurable _ (contDiff_coordinateCumulantGradient m h hμ hm).continuous a k)
    (fun a => D.observableNoise_progressive _ (contDiff_coordinateCumulantGradient m h hμ hm).continuous a k)
    (fun a => D.smoothObservableNoise_energy (coordinateCumulant μ m h) hf a k)
    Finset.univ (by norm_num : (0 : ℝ) < 1)
  rw [D.cumulantNoise_eq_sum m h hμ hm]
  exact ⟨hm', hp, hq⟩

def cumulantNoiseIntegral (hμ : IsCompact μ.support) (hm : m ≠ 0)
    (k : Fin n) (T : ℝ) : Ω → ℝ :=
  stochasticIntegralBrownian (W.W k) ℱ (hW k) (D.cumulantNoise m h k)
    (D.cumulantNoise_admissible m h hμ hm k).1 (D.cumulantNoise_admissible m h hμ hm k).2.1
    (D.cumulantNoise_admissible m h hμ hm k).2.2 T

theorem cumulantNoiseIntegral_eq_sum (hμ : IsCompact μ.support) (hm : m ≠ 0)
    (k : Fin n) {T : ℝ} (hT : 0 < T) : D.cumulantNoiseIntegral m h hμ hm k T =ᵐ[P]
      fun ω => ∑ a : Fin (n+n*n), D.smoothObservableNoiseIntegral (coordinateCumulant μ m h)
        (contDiff_coordinateCumulant hμ hm h) a k T ω := by
  have hf := contDiff_coordinateCumulant hμ hm h
  obtain ⟨hm', hp, hq, he⟩ := exists_stochasticIntegralBrownian_finsetSum (W.W k) ℱ (hW k)
    (fun a : Fin (n+n*n) => D.observableNoise (coordinateCumulantGradient μ m h) a k)
    (fun a => D.observableNoise_measurable _ (contDiff_coordinateCumulantGradient m h hμ hm).continuous a k)
    (fun a => D.observableNoise_progressive _ (contDiff_coordinateCumulantGradient m h hμ hm).continuous a k)
    (fun a => D.smoothObservableNoise_energy (coordinateCumulant μ m h) hf a k)
    Finset.univ hT
  unfold cumulantNoiseIntegral
  rw [stochasticIntegralBrownian_congr_fun (W.W k) ℱ (hW k) (D.cumulantNoise_eq_sum m h hμ hm k)
    (D.cumulantNoise_admissible m h hμ hm k).1 (D.cumulantNoise_admissible m h hμ hm k).2.1
    (D.cumulantNoise_admissible m h hμ hm k).2.2 hm' hp hq T]
  exact he

/-- Literal local equation (73), stopped only at the actual parameter exit.
The Brownian integrands are next cumulants in the principal whitening directions. -/
theorem cumulant_equation (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (hm : 3 ≤ m) (i₀ : Fin m)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[ℱ 0] A)
    {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, (T : WithTop ℝ) ≤ D.exit ω →
      coordinateCumulant μ m h (D.pair.Y T ω) - cumulantTensor μ m h =
        -(∫ t in Icc (0 : ℝ) T,
          (m : ℝ) * coordinateCumulant μ m h (D.pair.Y t ω) +
            lowerCumulantDrift μ h (D.pair.Y t ω) i₀ ∂volume) +
          ∑ k : Fin n, D.cumulantNoiseIntegral m h hμ (by omega) k T ω := by
  have hm0 : m ≠ 0 := by omega
  have hi := D.itoFormula_original_smooth (coordinateCumulant μ m h)
    (contDiff_coordinateCumulant hμ hm0 h) hℱ0 hnull hT
  have hg : observableGenerator (coordinateDrift μ) (coordinateDiffusion μ)
      (coordinateCumulantGradient μ m h) (coordinateCumulantHessian μ m h) =
        fun z => -((m : ℝ) * coordinateCumulant μ m h z + lowerCumulantDrift μ h z i₀) := by
    funext z
    rw [observableGenerator_coordinateCumulant, cumulantGenerator_eq_neg_order_add_lower hμ hfull hm]
  have hn : ∀ᵐ ω ∂P, ∀ k : Fin n,
      D.cumulantNoiseIntegral m h hμ hm0 k T ω =
        ∑ a : Fin (n+n*n), D.smoothObservableNoiseIntegral (coordinateCumulant μ m h)
          (contDiff_coordinateCumulant hμ hm0 h) a k T ω :=
    ae_all_iff.mpr fun k => D.cumulantNoiseIntegral_eq_sum m h hμ hm0 k hT
  filter_upwards [hi, D.initial_Y, hn] with ω hI h0 hnoise hle
  have he := hI hle
  change coordinateCumulant μ m h (D.pair.Y T ω) - coordinateCumulant μ m h (D.pair.Y 0 ω) =
    (∫ t in Icc (0 : ℝ) T, observableGenerator (coordinateDrift μ) (coordinateDiffusion μ)
      (coordinateCumulantGradient μ m h) (coordinateCumulantHessian μ m h) (D.pair.Y t ω) ∂volume) + _ at he
  rw [hg, integral_neg] at he
  have hs : (∑ a : Fin (n+n*n), ∑ k : Fin n,
      D.smoothObservableNoiseIntegral (coordinateCumulant μ m h) (contDiff_coordinateCumulant hμ hm0 h) a k T ω) =
      ∑ k : Fin n, D.cumulantNoiseIntegral m h hμ hm0 k T ω := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => (hnoise k).symm
  rw [hs, h0] at he
  simpa only [coordinateCumulant, decodeState_zero, Prod.fst_zero, Prod.snd_zero, law_zero_zero] using he

end BallProcess
end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.BallProcess.cumulant_equation

import KLS.AdaptiveCoordinateGenerator
import KLS.LocalObservableGenerator
import LevyStochCalc.Brownian.ItoFinsetSum

/-! The actual third-cumulant Brownian coefficient of the adaptive covariance. -/
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

def supportNormBound (hμ : IsCompact μ.support) : ℝ :=
  Classical.choose hμ.isBounded.exists_pos_norm_le

theorem supportNormBound_pos (hμ : IsCompact μ.support) : 0 < supportNormBound hμ :=
  (Classical.choose_spec hμ.isBounded.exists_pos_norm_le).1

theorem norm_le_supportNormBound (hμ : IsCompact μ.support) (x : Space n) (hx : x ∈ μ.support) :
    ‖x‖ ≤ supportNormBound hμ :=
  (Classical.choose_spec hμ.isBounded.exists_pos_norm_le).2 x hx

def covarianceGradientBound (hμ : IsCompact μ.support) : ℝ :=
  coordinateCovarianceDerivativeBound n (supportNormBound hμ)

theorem covarianceGradientBound_nonneg (hμ : IsCompact μ.support) : 0 ≤ covarianceGradientBound hμ :=
  coordinateCovarianceDerivativeBound_nonneg (supportNormBound_pos hμ).le

theorem covarianceGradient_norm_le (hμ : IsCompact μ.support) (i j : Fin n)
    (z : Fin (n+n*n) → ℝ) : ‖coordinateCovarianceGradient μ i j z‖ ≤ covarianceGradientBound hμ :=
  norm_coordinateCovarianceGradient_le hμ (supportNormBound_pos hμ).le (norm_le_supportNormBound hμ) i j z

def covarianceNoiseCoefficient (μ : Measure (Space n)) (i j k : Fin n) (z : Fin (n+n*n) → ℝ) : ℝ :=
  coordinateCovarianceGradient μ i j z (coordinateDiffusion μ k z)

theorem covarianceNoiseCoefficient_eq_thirdCumulant (hμ : IsCompact μ.support)
    (i j k : Fin n) (z : Fin (n+n*n) → ℝ) :
    covarianceNoiseCoefficient μ i j k z =
      tiltThirdCumulant μ (exponent (decodeState z).1 (decodeState z).2)
        (fun x => x i) (fun x => x j) (projection μ (decodeState z) k) := by
  unfold covarianceNoiseCoefficient
  rw [coordinateCovarianceGradient_apply hμ, coordinateDiffusion, decode_encodeState,
    covarianceGradient_apply_eq_cumulant hμ, exponent_diffusion_eq_projection]

theorem covarianceNoiseCoefficient_eq_sum (i j k : Fin n) (z : Fin (n+n*n) → ℝ) :
    covarianceNoiseCoefficient μ i j k z = ∑ a : Fin (n+n*n),
      coordDeriv (coordinateCovarianceGradient μ i j) a z * coordinateDiffusion μ k z a := by
  unfold covarianceNoiseCoefficient
  rw [apply_eq_sum_coordDeriv]
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {W : MultidimBrownianMotion P n} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ} {R : ℝ}
namespace BallProcess
variable (D : BallProcess μ W ℱ hW R)

def covarianceNoise (i j k : Fin n) : Ω → ℝ → ℝ :=
  Probability.stopped D.exit (fun ω t => covarianceNoiseCoefficient μ i j k (D.pair.Y t ω))

theorem covarianceNoise_eq_sum (i j k : Fin n) : D.covarianceNoise i j k =
    fun ω t => ∑ a : Fin (n+n*n), D.observableNoise (coordinateCovarianceGradient μ i j) a k ω t := by
  funext ω t
  simp only [covarianceNoise, LocalProcess.observableNoise, LocalProcess.noise, Probability.stopped]
  by_cases ht : (t : WithTop ℝ) ≤ D.exit ω
  · simp only [ht, ite_true, covarianceNoiseCoefficient_eq_sum]
  · simp only [ht, ite_false, mul_zero, Finset.sum_const_zero]

theorem covarianceNoise_admissible (hμ : IsCompact μ.support) (i j k : Fin n) :
    Measurable (Function.uncurry (D.covarianceNoise i j k)) ∧
    Probability.ProgressivelyMeasurable ℱ (D.covarianceNoise i j k) ∧
    ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ t in Icc (0 : ℝ) T,
      (‖D.covarianceNoise i j k ω t‖₊ : ℝ≥0∞)^2 ∂volume ∂P < ⊤ := by
  obtain ⟨hm, hp, hq, _⟩ := exists_stochasticIntegralBrownian_finsetSum (W.W k) ℱ (hW k)
    (fun a : Fin (n+n*n) => D.observableNoise (coordinateCovarianceGradient μ i j) a k)
    (fun a => D.observableNoise_measurable _ (contDiff_coordinateCovarianceGradient hμ i j).continuous a k)
    (fun a => D.observableNoise_progressive _ (contDiff_coordinateCovarianceGradient hμ i j).continuous a k)
    (fun a => D.observableNoise_energy _ (covarianceGradientBound_nonneg hμ) (covarianceGradient_norm_le hμ i j) a k)
    Finset.univ (by norm_num : (0 : ℝ) < 1)
  rw [D.covarianceNoise_eq_sum]
  exact ⟨hm, hp, hq⟩

def covarianceNoiseIntegral (hμ : IsCompact μ.support) (i j k : Fin n) (T : ℝ) : Ω → ℝ :=
  stochasticIntegralBrownian (W.W k) ℱ (hW k) (D.covarianceNoise i j k)
    (D.covarianceNoise_admissible hμ i j k).1 (D.covarianceNoise_admissible hμ i j k).2.1
    (D.covarianceNoise_admissible hμ i j k).2.2 T

theorem covarianceNoiseIntegral_eq_sum (hμ : IsCompact μ.support) (i j k : Fin n)
    {T : ℝ} (hT : 0 < T) : D.covarianceNoiseIntegral hμ i j k T =ᵐ[P]
      fun ω => ∑ a : Fin (n+n*n), D.observableNoiseIntegral (coordinateCovarianceGradient μ i j)
        (contDiff_coordinateCovarianceGradient hμ i j).continuous
        (covarianceGradientBound_nonneg hμ) (covarianceGradient_norm_le hμ i j) a k T ω := by
  obtain ⟨hm, hp, hq, he⟩ := exists_stochasticIntegralBrownian_finsetSum (W.W k) ℱ (hW k)
    (fun a : Fin (n+n*n) => D.observableNoise (coordinateCovarianceGradient μ i j) a k)
    (fun a => D.observableNoise_measurable _ (contDiff_coordinateCovarianceGradient hμ i j).continuous a k)
    (fun a => D.observableNoise_progressive _ (contDiff_coordinateCovarianceGradient hμ i j).continuous a k)
    (fun a => D.observableNoise_energy _ (covarianceGradientBound_nonneg hμ) (covarianceGradient_norm_le hμ i j) a k)
    Finset.univ hT
  unfold covarianceNoiseIntegral
  rw [stochasticIntegralBrownian_congr_fun (W.W k) ℱ (hW k) (D.covarianceNoise_eq_sum i j k)
    (D.covarianceNoise_admissible hμ i j k).1 (D.covarianceNoise_admissible hμ i j k).2.1
    (D.covarianceNoise_admissible hμ i j k).2.2 hm hp hq T]
  exact he

end BallProcess
end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.BallProcess.covarianceNoiseIntegral_eq_sum
#print axioms KLS.AdaptiveLocalization.covarianceNoiseCoefficient_eq_thirdCumulant

import KLS.AdaptivePathLogDetBounds

/-! Globally bounded coefficients agreeing with the true logdet coefficients before lifetime. -/
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped NNReal ENNReal Topology BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
namespace KLS.LocalDiffusion

def clampScalar (K x : ℝ) : ℝ := max (-K) (min x K)

theorem continuous_clampScalar (K : ℝ) : Continuous (clampScalar K) :=
  continuous_const.max (continuous_id.min continuous_const)

theorem abs_clampScalar_le {K : ℝ} (hK : 0 ≤ K) (x : ℝ) : |clampScalar K x| ≤ K := by
  apply abs_le.mpr
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩

theorem clampScalar_eq {K x : ℝ} (hx : |x| ≤ K) : clampScalar K x = x := by
  rw [clampScalar, min_eq_left (abs_le.mp hx).2, max_eq_right (abs_le.mp hx).1]

end KLS.LocalDiffusion
namespace KLS.AdaptiveLocalization
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
open LevyStochCalc.Brownian.Ito LevyStochCalc.Ito.Picard KLS.LocalDiffusion KLSLevyProbe
universe u
variable {n : ℕ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {μ : Measure (Space n)} [IsProbabilityMeasure μ]
  {W : MultidimBrownianMotion P n} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ}

def logDetNoiseBound (n : ℕ) : ℝ := (n : ℝ)*normalizedThirdMomentBound n

def logDetDriftBound (n : ℕ) : ℝ :=
  (n : ℝ) + 1/2 * (n : ℝ)^3*(normalizedThirdMomentBound n)^2

theorem logDetNoiseBound_nonneg (n : ℕ) : 0 ≤ logDetNoiseBound n :=
  mul_nonneg (Nat.cast_nonneg n) (normalizedThirdMomentBound_pos n).le

theorem logDetDriftBound_nonneg (n : ℕ) : 0 ≤ logDetDriftBound n := by
  unfold logDetDriftBound
  positivity

namespace MaximalProcess
variable (D : MaximalProcess μ W ℱ hW)

include D in
theorem continuous_logDetTraceCorrection (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) : Continuous (logDetTraceCorrection μ) := by
  have hI : Continuous (fun z : Fin (n+n*n) → ℝ => (coordinateCovarianceMatrix μ z)⁻¹) :=
    (contDiff_inverseCovariance hμ hfull).continuous.comp contDiff_decodeState.continuous
  have hC (k : Fin n) : Continuous (covarianceNoiseMatrix μ k) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact (contDiff_coordinateCovarianceGradient hμ i j).continuous.clm_apply ((D 0).diffusion_continuous k)
  unfold logDetTraceCorrection
  exact continuous_finset_sum _ fun k _ => (((hI.mul (hC k)).mul hI).mul (hC k)).matrix_trace

def clippedLogDetNoise (k : Fin n) : Ω → ℝ → ℝ :=
  fun ω t => clampScalar (logDetNoiseBound n) (logDetNoiseCoefficient μ k (D.path t ω))

theorem clippedLogDetNoise_bound (k : Fin n) (ω : Ω) (t : ℝ) :
    |D.clippedLogDetNoise k ω t| ≤ logDetNoiseBound n :=
  abs_clampScalar_le (logDetNoiseBound_nonneg n) _

theorem clippedLogDetNoise_measurable (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (k : Fin n) :
    Measurable (Function.uncurry (D.clippedLogDetNoise k)) :=
  ((continuous_clampScalar _).comp (D.continuous_logDetNoiseCoefficient hμ hfull k)).measurable.comp D.measurable_path

theorem clippedLogDetNoise_progressive (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (k : Fin n) :
    Probability.ProgressivelyMeasurable ℱ (D.clippedLogDetNoise k) :=
  progressivelyMeasurable_comp_state
    (f := fun _ z => clampScalar (logDetNoiseBound n) (logDetNoiseCoefficient μ k z)) D.progressive_path
    (((continuous_clampScalar _).comp (D.continuous_logDetNoiseCoefficient hμ hfull k)).measurable.comp measurable_snd)

theorem clippedLogDetNoise_energy (k : Fin n) (T : ℝ) (hT : 0 < T) :
    (∫⁻ ω, ∫⁻ t in Icc (0 : ℝ) T,
      (‖D.clippedLogDetNoise k ω t‖₊ : ℝ≥0∞)^2 ∂volume ∂P) < ⊤ :=
  energy_lt_top_of_bounded (D.clippedLogDetNoise_bound k) T hT

def clippedLogDetNoiseIntegral (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (k : Fin n) (T : ℝ) : Ω → ℝ :=
  stochasticIntegralBrownian (W.W k) ℱ (hW k) (D.clippedLogDetNoise k)
    (D.clippedLogDetNoise_measurable hμ hfull k) (D.clippedLogDetNoise_progressive hμ hfull k)
    (D.clippedLogDetNoise_energy k) T

def clippedLogDetDrift : Ω → ℝ → ℝ := fun ω t => clampScalar (logDetDriftBound n)
  (-(n : ℝ) - 1/2 * logDetTraceCorrection μ (D.path t ω))

theorem clippedLogDetDrift_bound (ω : Ω) (t : ℝ) :
    |D.clippedLogDetDrift ω t| ≤ logDetDriftBound n :=
  abs_clampScalar_le (logDetDriftBound_nonneg n) _

theorem clippedLogDetDrift_measurable (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) : Measurable (Function.uncurry D.clippedLogDetDrift) :=
  ((continuous_clampScalar _).comp (continuous_const.sub
    (continuous_const.mul (D.continuous_logDetTraceCorrection hμ hfull)))).measurable.comp D.measurable_path

theorem ae_all_clippedLogDet_eq (hμ : IsCompact μ.support) (hadm : admissibleMeasure μ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) < D.lifetime ω →
      (∀ k : Fin n, D.clippedLogDetNoise k ω t = logDetNoiseCoefficient μ k (D.path t ω)) ∧
      (D.clippedLogDetDrift ω t = -(n : ℝ) - 1/2 * logDetTraceCorrection μ (D.path t ω)) := by
  filter_upwards [D.ae_all_logDet_bounds hμ hadm] with ω hb t ht hlife
  obtain ⟨hn, hq0, hq, _⟩ := hb t ht hlife
  constructor
  · intro k
    exact clampScalar_eq (hn k)
  · apply clampScalar_eq
    unfold logDetDriftBound
    apply abs_le.mpr
    constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) n,
      mul_nonneg (pow_nonneg (Nat.cast_nonneg (α := ℝ) n) 3) (sq_nonneg (normalizedThirdMomentBound n))]

end MaximalProcess
end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.MaximalProcess.ae_all_clippedLogDet_eq

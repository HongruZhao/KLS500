import KLS.ConstructedMaximalLocalSde
import KLS.AdaptiveLocalProcess

/-! The actual adaptive localization SDE is assembled up to its maximal lifetime. -/
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix.Norms.Elementwise
noncomputable section
namespace KLS.AdaptiveLocalization
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
open LevyStochCalc.Brownian.Ito KLS.LocalDiffusion KLSLevyProbe
universe u
variable {n : ℕ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {μ : Measure (Space n)} [IsProbabilityMeasure μ]
  {W : MultidimBrownianMotion P n} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ}

abbrev MaximalProcess (μ : Measure (Space n)) (W : MultidimBrownianMotion P n)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hW : ∀ k, IsBrownianFiltration (W.W k) ℱ) :=
  LocalProcessFamily W ℱ hW (coordinateDrift μ) (coordinateDiffusion μ)

namespace MaximalProcess
variable (D : MaximalProcess μ W ℱ hW)

def parameterPath (t : ℝ) (ω : Ω) : Parameter n := decodeState (D.path t ω)

theorem parameterPath_initial : ∀ᵐ ω ∂P, D.parameterPath 0 ω = 0 := by
  filter_upwards [D.path_initial] with ω hω
  simp only [parameterPath, hω, decodeState_zero, Pi.zero_apply]

theorem parameterPath_continuousOn : ∀ᵐ ω ∂P,
    ContinuousOn (fun t => D.parameterPath t ω)
      {t : ℝ | 0 ≤ t ∧ (t : WithTop ℝ) < D.lifetime ω} :=
  D.ae_continuousOn_before_lifetime.mono fun ω hω =>
    contDiff_decodeState.continuous.comp_continuousOn hω

theorem linear_noise_eq (m : ℕ) (i k : Fin n) (ω : Ω) (t : ℝ) :
    D.noise m (Fin.castAdd (n*n) i) k ω t =
      Probability.stopped (D.exit m)
        (fun ω t => inverseSqrtCovariance μ (D.parameterPath t ω) i k) ω t := by
  unfold LocalProcessFamily.noise Probability.stopped
  simp only [coordinateDiffusion_linear, parameterPath]

theorem linear_equation (m : ℕ) (i : Fin n) {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, (T : WithTop ℝ) ≤ D.exit m ω →
      (D.parameterPath T ω).1 i =
        (∫ t in Icc (0 : ℝ) T, linearDrift μ (D.parameterPath t ω) i ∂volume) +
        ∑ k : Fin n, D.noiseIntegral m (Fin.castAdd (n*n) i) k T ω := by
  filter_upwards [D.originalEquation m hT] with ω hω hle
  have hi := hω hle (Fin.castAdd (n*n) i)
  simpa only [parameterPath, decodeState, coordinateDrift_linear] using hi

theorem matrix_equation (m : ℕ) (i j : Fin n) {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, (T : WithTop ℝ) ≤ D.exit m ω →
      (D.parameterPath T ω).2 i j =
        ∫ t in Icc (0 : ℝ) T, inverseCovariance μ (D.parameterPath t ω) i j ∂volume := by
  have hn : ∀ᵐ ω ∂P, ∀ k : Fin n,
      D.noiseIntegral m (Fin.natAdd n (finProdFinEquiv (i,j))) k T ω = 0 := by
    apply ae_all_iff.mpr
    intro k
    have hi := D.noiseIntegral_eq_local m (Fin.natAdd n (finProdFinEquiv (i,j))) k hT
    have hz := BallProcess.matrix_noiseIntegral_zero (D m) i j k T
    filter_upwards [hi, hz] with ω hiω hzω
    exact hiω.trans hzω
  filter_upwards [D.originalEquation m hT, hn] with ω hω hnω hle
  have hi := hω hle (Fin.natAdd n (finProdFinEquiv (i,j)))
  simp only [hnω, Finset.sum_const_zero, add_zero, coordinateDrift_matrix] at hi
  exact hi

end MaximalProcess

/-- Construct the actual adaptive SDE with its maximal lifetime, from compact
full-dimensional probability data only. The lifetime is not asserted infinite. -/
theorem exists_adaptiveMaximalLocalProcess (μ : Measure (Space n)) [IsProbabilityMeasure μ]
    (hμ : IsCompact μ.support) (hfull : affineSpan ℝ μ.support = ⊤) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (W : MultidimBrownianMotion P n)
      (D : MaximalProcess μ W (usualFiltration W) (usualFiltration_brownian W)),
      IsMaximalLocalSde D :=
  exists_constructed_maximalLocalSde (coordinateDrift μ) (coordinateDiffusion μ)
    (locallyLipschitz_coordinateDrift hμ hfull) (locallyLipschitz_coordinateDiffusion hμ hfull)

theorem exists_adaptiveMaximalLocalProcess_of_isotropic (μ : Measure (Space n))
    [IsProbabilityMeasure μ] (hμ : IsCompact μ.support) (hiso : IsIsotropic μ) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (W : MultidimBrownianMotion P n)
      (D : MaximalProcess μ W (usualFiltration W) (usualFiltration_brownian W)),
      IsMaximalLocalSde D :=
  exists_adaptiveMaximalLocalProcess μ hμ hiso.affineSpan_support_eq_top

end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.exists_adaptiveMaximalLocalProcess
#print axioms KLS.AdaptiveLocalization.MaximalProcess.linear_equation
#print axioms KLS.AdaptiveLocalization.MaximalProcess.matrix_equation

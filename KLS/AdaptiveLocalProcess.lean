import KLS.AdaptiveCoordinateState
import KLS.LocalProcessEquation
import LevyStochCalc.Brownian.ItoZero

/-! A genuinely constructed local adaptive localization SDE on every state ball. -/
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix.Norms.Elementwise
noncomputable section
namespace KLS.AdaptiveLocalization
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
open LevyStochCalc.Brownian.Ito KLS.LocalDiffusion KLSLevyProbe
universe u
variable {n : ℕ}

theorem coordinateDrift_linear (μ : Measure (Space n)) (z : Fin (n + n * n) → ℝ) (i : Fin n) :
    coordinateDrift μ z (Fin.castAdd (n * n) i) = linearDrift μ (decodeState z) i := by
  simp only [coordinateDrift, encodeState, Fin.addCases_left, drift]

theorem coordinateDrift_matrix (μ : Measure (Space n)) (z : Fin (n + n * n) → ℝ) (i j : Fin n) :
    coordinateDrift μ z (Fin.natAdd n (finProdFinEquiv (i,j))) =
      inverseCovariance μ (decodeState z) i j := by
  simp only [coordinateDrift, encodeState, Fin.addCases_right, Equiv.symm_apply_apply, drift]

theorem coordinateDiffusion_linear (μ : Measure (Space n)) (z : Fin (n + n * n) → ℝ) (i k : Fin n) :
    coordinateDiffusion μ k z (Fin.castAdd (n * n) i) = inverseSqrtCovariance μ (decodeState z) i k := by
  simp only [coordinateDiffusion, encodeState, Fin.addCases_left, diffusion]

theorem coordinateDiffusion_matrix (μ : Measure (Space n)) (z : Fin (n + n * n) → ℝ)
    (i j k : Fin n) : coordinateDiffusion μ k z (Fin.natAdd n (finProdFinEquiv (i,j))) = 0 := by
  simp only [coordinateDiffusion, encodeState, Fin.addCases_right, Equiv.symm_apply_apply,
    diffusion, Matrix.zero_apply]

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {μ : Measure (Space n)} [IsProbabilityMeasure μ]
  {W : MultidimBrownianMotion P n} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ} {R : ℝ}

abbrev BallProcess (μ : Measure (Space n)) (W : MultidimBrownianMotion P n)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hW : ∀ k, IsBrownianFiltration (W.W k) ℱ) (R : ℝ) :=
  LocalProcess W ℱ hW (coordinateDrift μ) (coordinateDiffusion μ) R

namespace BallProcess
variable (D : BallProcess μ W ℱ hW R)

def parameterPath (t : ℝ) (ω : Ω) : Parameter n := decodeState (D.pair.Y t ω)

theorem parameterPath_continuous (ω : Ω) : Continuous (fun t => D.parameterPath t ω) :=
  contDiff_decodeState.continuous.comp (D.pair.ito_Y.continuous_path ω)

theorem parameterPath_initial : ∀ᵐ ω ∂P, D.parameterPath 0 ω = 0 := by
  filter_upwards [D.initial_Y] with ω hω
  simp only [parameterPath, hω, decodeState_zero]

theorem linear_noise_eq (i k : Fin n) (ω : Ω) (t : ℝ) :
    D.noise (Fin.castAdd (n * n) i) k ω t =
      Probability.stopped D.exit (fun ω t => inverseSqrtCovariance μ (D.parameterPath t ω) i k) ω t := by
  unfold LocalProcess.noise Probability.stopped
  simp only [coordinateDiffusion_linear, parameterPath]

theorem matrix_noise_eq_zero (i j k : Fin n) :
    D.noise (Fin.natAdd n (finProdFinEquiv (i,j))) k = fun _ _ => 0 := by
  funext ω t
  simp only [LocalProcess.noise, Probability.stopped, coordinateDiffusion_matrix, ite_self]

theorem matrix_noiseIntegral_zero (i j k : Fin n) (T : ℝ) :
    D.noiseIntegral (Fin.natAdd n (finProdFinEquiv (i,j))) k T =ᵐ[P] 0 := by
  have hm : Measurable (Function.uncurry (fun (_ : Ω) (_ : ℝ) => (0 : ℝ))) := measurable_const
  have hp := Probability.progressivelyMeasurable_zero (Ω := Ω) (E := ℝ) ℱ
  have hq : ∀ T : ℝ, 0 < T → ∫⁻ _ω : Ω, ∫⁻ _t in Set.Icc (0 : ℝ) T,
      (‖(0 : ℝ)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by intros; simp
  have hi := stochasticIntegralBrownian_congr_fun (W.W k) ℱ (hW k)
    (D.matrix_noise_eq_zero i j k)
    (D.noise_measurable _ k) (D.noise_progressive _ k) (D.noise_energy _ k) hm hp hq T
  unfold LocalProcess.noiseIntegral
  rw [hi]
  exact stochasticIntegralBrownian_ae_zero (W.W k) ℱ (hW k) hm hp hq T

/-- The c equation has the actual A^{-1}a drift and stopped A^{-1/2} Brownian noise. -/
theorem linear_equation (i : Fin n) {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, (T : WithTop ℝ) ≤ D.exit ω →
      (D.parameterPath T ω).1 i =
        (∫ t in Set.Icc (0 : ℝ) T, linearDrift μ (D.parameterPath t ω) i ∂volume) +
        ∑ k : Fin n, D.noiseIntegral (Fin.castAdd (n * n) i) k T ω := by
  filter_upwards [D.originalEquation hT] with ω hω hle
  have hi := hω hle (Fin.castAdd (n * n) i)
  simpa only [parameterPath, decodeState, coordinateDrift_linear] using hi

/-- The Q equation is the actual integral of A^{-1}; its Brownian term is proved zero. -/
theorem matrix_equation (i j : Fin n) {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, (T : WithTop ℝ) ≤ D.exit ω →
      (D.parameterPath T ω).2 i j =
        ∫ t in Set.Icc (0 : ℝ) T, inverseCovariance μ (D.parameterPath t ω) i j ∂volume := by
  have hn : ∀ᵐ ω ∂P, ∀ k : Fin n,
      D.noiseIntegral (Fin.natAdd n (finProdFinEquiv (i,j))) k T ω = 0 :=
    ae_all_iff.mpr fun k => D.matrix_noiseIntegral_zero i j k T
  filter_upwards [D.originalEquation hT, hn] with ω hω hnω hle
  have hi := hω hle (Fin.natAdd n (finProdFinEquiv (i,j)))
  simp only [hnω, Finset.sum_const_zero, add_zero, coordinateDrift_matrix] at hi
  exact hi

end BallProcess

/-- For every compact probability measure with full affine support, construct
one Brownian driver and, on each positive state ball, the actual adaptive SDE
up to a strictly positive genuine stopping time. No global solution is a premise. -/
theorem exists_adaptiveLocalProcesses (μ : Measure (Space n)) [IsProbabilityMeasure μ]
    (hμ : IsCompact μ.support) (hfull : affineSpan ℝ μ.support = ⊤) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (W : MultidimBrownianMotion P n), ∀ R : ℝ, 0 < R →
      ∃ D : BallProcess μ W (usualFiltration W) (usualFiltration_brownian W) R,
        (∀ᵐ ω ∂P, (0 : WithTop ℝ) < D.exit ω) ∧
        (∀ T : ℝ, 0 < T → D.OriginalEquation T) := by
  obtain ⟨Ω, mΩ, P, hP, W, hloc⟩ := exists_constructed_localProcesses
    (coordinateDrift μ) (coordinateDiffusion μ)
    (locallyLipschitz_coordinateDrift hμ hfull) (locallyLipschitz_coordinateDiffusion hμ hfull)
  refine ⟨Ω, mΩ, P, hP, W, ?_⟩
  intro R hR
  obtain ⟨D⟩ := hloc R hR
  exact ⟨D, D.exit_pos hR, fun T hT => D.originalEquation hT⟩

theorem exists_adaptiveLocalProcesses_of_isotropic (μ : Measure (Space n)) [IsProbabilityMeasure μ]
    (hμ : IsCompact μ.support) (hiso : IsIsotropic μ) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (W : MultidimBrownianMotion P n), ∀ R : ℝ, 0 < R →
      ∃ D : BallProcess μ W (usualFiltration W) (usualFiltration_brownian W) R,
        (∀ᵐ ω ∂P, (0 : WithTop ℝ) < D.exit ω) ∧
        (∀ T : ℝ, 0 < T → D.OriginalEquation T) :=
  exists_adaptiveLocalProcesses μ hμ hiso.affineSpan_support_eq_top

end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.exists_adaptiveLocalProcesses
#print axioms KLS.AdaptiveLocalization.BallProcess.linear_equation
#print axioms KLS.AdaptiveLocalization.BallProcess.matrix_equation

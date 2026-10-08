import KLS.LocalFamilyClippedCoefficients

/-! Genuine stopping times at which a local path's original coefficients reach a clip radius. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology
noncomputable section
namespace KLS.LocalDiffusion.LocalProcessFamily
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
open LevyStochCalc.Brownian.Ito LevyStochCalc.Ito.Picard
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {N d : ℕ} {W : MultidimBrownianMotion P d} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ}
  {b : (Fin N → ℝ) → Fin N → ℝ} {s : Fin d → (Fin N → ℝ) → Fin N → ℝ}
  (D : LocalProcessFamily W ℱ hW b s)

def coefficientExit (m L : ℕ) : Ω → WithTop ℝ :=
  Probability.exitTime (fun ω t => D.coefficientVector ((D m).pair.Y t ω)) (D.coefficientClipRadius L)

def jointCoefficientExit (m L : ℕ) : Ω → WithTop ℝ :=
  fun ω => min (D.exit m ω) (D.coefficientExit m L ω)

theorem coefficientExit_isStoppingTime (m L : ℕ) : IsStoppingTime ℱ (D.coefficientExit m L) :=
  Probability.isStoppingTime_exitTime
    (fun t => D.continuous_coefficientVector.measurable.comp ((D m).pair.ito_Y.adapted t).measurable)
    (fun ω => D.continuous_coefficientVector.comp ((D m).pair.ito_Y.continuous_path ω)) _

theorem jointCoefficientExit_isStoppingTime (m L : ℕ) : IsStoppingTime ℱ (D.jointCoefficientExit m L) :=
  (D.exit_isStoppingTime m).min (D.coefficientExit_isStoppingTime m L)

theorem ae_coefficient_bound_before_joint (m L : ℕ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) ≤ D.jointCoefficientExit m L ω →
      ‖D.coefficientVector (D.path t ω)‖ ≤ D.coefficientClipRadius L := by
  filter_upwards [D.ae_path_eq_of_le_exit, (D m).initial_Y] with ω hp h0 t ht he
  have he' := le_min_iff.mp he
  rw [hp m t ht he'.1]
  rcases eq_or_lt_of_le ht with h | h
  · rw [← h, h0]
    unfold coefficientClipRadius
    linarith [Nat.cast_nonneg (α := ℝ) L]
  · exact Probability.norm_le_of_le_exitTime
      (D.continuous_coefficientVector.comp ((D m).pair.ito_Y.continuous_path ω)) h he'.2

theorem ae_clipped_eq_before_joint (m L : ℕ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) ≤ D.jointCoefficientExit m L ω →
      (∀ i : Fin N, D.clippedDrift L i ω t = b (D.path t ω) i) ∧
      (∀ (i : Fin N) (k : Fin d), D.clippedNoise L i k ω t = s k (D.path t ω) i) := by
  filter_upwards [D.ae_coefficient_bound_before_joint m L] with ω hb t ht he
  have hn := hb t ht he
  have hnorm : ‖b (D.path t ω)‖ ≤ D.coefficientClipRadius L ∧
      ‖fun k => s k (D.path t ω)‖ ≤ D.coefficientClipRadius L := by
    simpa only [coefficientVector, Prod.norm_def, max_le_iff] using hn
  constructor
  · intro i
    apply clampScalar_eq
    exact (norm_le_pi_norm (b (D.path t ω)) i).trans hnorm.1
  · intro i k
    apply clampScalar_eq
    exact ((norm_le_pi_norm (s k (D.path t ω)) i).trans
      (norm_le_pi_norm (fun k => s k (D.path t ω)) k)).trans hnorm.2

end KLS.LocalDiffusion.LocalProcessFamily
end
#print axioms KLS.LocalDiffusion.LocalProcessFamily.ae_clipped_eq_before_joint

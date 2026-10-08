import KLS.AdaptiveAverageMartingale

/-! Fixed spatial exponential observables, with genuine global martingale evolution. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS.AdaptiveLocalization
variable {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

def exponentialObservable (w : Space n) (x : Space n) : ℝ := Real.exp (inner ℝ w x)

theorem continuous_exponentialObservable (w : Space n) : Continuous (exponentialObservable w) := by
  unfold exponentialObservable
  fun_prop

theorem exponentialObservable_bound (hμ : IsCompact μ.support) (w : Space n)
    (x : Space n) (hx : x ∈ μ.support) :
    |exponentialObservable w x| ≤ Real.exp (‖w‖ * supportNormBound hμ) := by
  rw [exponentialObservable, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr ((real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_left (norm_le_supportNormBound hμ x hx) (norm_nonneg _)))

theorem exponentialObservable_lower_bound (hμ : IsCompact μ.support) (w : Space n)
    (x : Space n) (hx : x ∈ μ.support) :
    Real.exp (-(‖w‖ * supportNormBound hμ)) ≤ exponentialObservable w x := by
  apply Real.exp_le_exp.mpr
  have h := (abs_real_inner_le_norm w x).trans
    (mul_le_mul_of_nonneg_left (norm_le_supportNormBound hμ x hx) (norm_nonneg _))
  exact (abs_le.mp h).1

theorem coordinateMGF_bounds (hμ : IsCompact μ.support) (w : Space n)
    (z : Fin (n+n*n) → ℝ) :
    Real.exp (-(‖w‖ * supportNormBound hμ)) ≤ coordinateAverage μ (exponentialObservable w) z ∧
      coordinateAverage μ (exponentialObservable w) z ≤ Real.exp (‖w‖ * supportNormBound hμ) := by
  let p := decodeState z
  let := law_isProbability hμ p.1 p.2
  have hi := integrable_law_of_integrable hμ
    (integrable_of_bounded_on_support (continuous_exponentialObservable w).measurable
      (exponentialObservable_bound hμ w)) p
  constructor
  · have hb : ∀ᵐ x ∂law μ p.1 p.2,
        Real.exp (-(‖w‖ * supportNormBound hμ)) ≤ exponentialObservable w x := by
      filter_upwards [(law μ p.1 p.2).support_mem_ae] with x hx
      exact exponentialObservable_lower_bound hμ w x (by rwa [support_law hμ] at hx)
    have hh := integral_mono_ae (integrable_const (Real.exp (-(‖w‖ * supportNormBound hμ)))) hi hb
    simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul, coordinateAverage, p] using hh
  · exact (le_abs_self _).trans (abs_coordinateAverage_le hμ (exponentialObservable_bound hμ w) z)

theorem coordinateMGF_pos (hμ : IsCompact μ.support) (w : Space n)
    (z : Fin (n+n*n) → ℝ) : 0 < coordinateAverage μ (exponentialObservable w) z :=
  (Real.exp_pos _).trans_le (coordinateMGF_bounds hμ w z).1

open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
open LevyStochCalc.Brownian.Ito KLS.LocalDiffusion KLSLevyProbe
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {W : MultidimBrownianMotion P n} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ}
namespace MaximalProcess
variable (D : MaximalProcess μ W ℱ hW)

/-- The actual moment-generating function of the constructed localization law. -/
def mgfPath (w : Space n) (t : ℝ) (ω : Ω) : ℝ :=
  ∫ x, Real.exp (inner ℝ w x) ∂D.localizationLaw t ω

theorem mgfPath_pos (hμ : IsCompact μ.support) (w : Space n) (t : ℝ) (ω : Ω) :
    0 < D.mgfPath w t ω := coordinateMGF_pos hμ w (D.path t ω)

variable (hμ : IsCompact μ.support) (hadm : admissibleMeasure μ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[ℱ 0] A)

include hμ hadm hℱ0 hnull in
/-- For each fixed spatial vector, the literal MGF is a bounded martingale. -/
theorem mgfPath_martingale (w : Space n) :
    Martingale (fun t : ℝ≥0 => D.mgfPath w (t : ℝ)) (nonnegativeFiltration ℱ) P :=
  D.averagePath_martingale (exponentialObservable w) hμ hadm (continuous_exponentialObservable w).measurable
    (Real.exp_pos _).le (exponentialObservable_bound hμ w) hℱ0 hnull

include hμ hadm hℱ0 hnull in
theorem mgfPath_equation_global (w : Space n) {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, D.mgfPath w T ω - (∫ x, Real.exp (inner ℝ w x) ∂μ) =
      ∑ k : Fin n, D.globalAverageNoiseIntegral (exponentialObservable w) hμ hadm
        (continuous_exponentialObservable w).measurable (Real.exp_pos _).le
        (exponentialObservable_bound hμ w) hℱ0 hnull k T ω :=
  D.average_equation_global (exponentialObservable w) hμ hadm (continuous_exponentialObservable w).measurable
    (Real.exp_pos _).le (exponentialObservable_bound hμ w) hℱ0 hnull hT

end MaximalProcess
end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.MaximalProcess.mgfPath_martingale
#print axioms KLS.AdaptiveLocalization.MaximalProcess.mgfPath_equation_global

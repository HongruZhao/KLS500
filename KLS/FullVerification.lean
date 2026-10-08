import KLS.FullQuadraticVarianceBound
import KLS.QuadraticEightFullPoincare
import KLS.ClassToDensity
import KLS.RealEndpoint
import KLS.FullClassCheegerConversion

open MeasureTheory
open scoped ENNReal NNReal
noncomputable section
namespace KLS

/-- The genuine quadratic inequality holds in every finite dimension. -/
theorem universalQuadraticVarianceEight :
    ∀ n, ∀ μ : Measure (Space n), admissibleMeasure μ → QuadraticVarianceEight μ := by
  intro n μ hμ
  exact hμ.quadraticVarianceEight_unconditional

/-- A certified sufficient numerical bound for the actual universal optimum. -/
theorem universalPoincareConstant_le_certified :
    universalPoincareConstant ≤ ENNReal.ofReal 126663739519795200 :=
  universalPoincareConstant_le_of_universalQuadratic universalQuadraticVarianceEight

/-- Finiteness of the actual universal Poincare constant. -/
theorem universalPoincareConstant_finite : universalPoincareConstant < ⊤ :=
  universalPoincareConstant_le_certified.trans_lt ENNReal.ofReal_lt_top

/-- The explicit bound is a faithful constant for the full test class. -/
theorem admissibleMeasure.certified_poincare_mem
    {n : ℕ} (hn : 1 ≤ n) {μ : Measure (Space n)} (hμ : admissibleMeasure μ) :
    (126663739519795200 : ℝ≥0) ∈ poincareConstants μ := by
  have hle := (poincareConstant_le_universal hn hμ).trans universalPoincareConstant_le_certified
  have hne := poincareConstants_nonempty_iff.mpr (hle.trans_lt ENNReal.ofReal_lt_top)
  apply (poincareConstants_iff_optimal_le hne (hμ.poincareConstant_pos hn)).mpr
  simpa using hle

/-- All clauses of the original full-class Poincare target hold, including
finite-energy integrability and the separate L2 convention. -/
theorem fullPoincareVerification : FullPoincareVerification := by
  refine ⟨126663739519795200, by norm_num,
    universalPoincareConstant_le_certified, universalPoincareConstant_finite, ?_,
    fullFiniteEnergyPoincare_of_universal_finite universalPoincareConstant_finite,
    fullL2Poincare_of_universal_finite universalPoincareConstant_finite⟩
  intro n hn μ hμ
  exact ⟨hμ.one_le_poincareConstant hn, poincareConstant_le_universal hn hμ⟩

/-- The literal real-integral inequality, after finite energy has supplied
all necessary integrability. -/
theorem admissibleMeasure.certified_real_poincare
    {n : ℕ} (hn : 1 ≤ n) {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : LocallyLipschitz f) (he : energy μ f < ⊤) :
    MemLp f 2 μ ∧ Integrable (fun x => ‖gradient f x‖ ^ 2) μ ∧
      ((∫ x, (f x) ^ 2 ∂μ) - (∫ x, f x ∂μ) ^ 2 ≤
        126663739519795200 * ∫ x, ‖gradient f x‖ ^ 2 ∂μ) := by
  let : IsProbabilityMeasure μ := hμ.isProb
  simpa using finiteEnergy_real_poincare_of_mem_constants hμ.absolutelyContinuousLebesgue
    (hμ.certified_poincare_mem hn) hf he

/-- An explicit dimension-independent Cheeger bound on the original full
compact-set log-concave class. Optimality is not asserted. -/
theorem admissibleMeasure.certified_cheeger_lower
    {n : ℕ} (hn : 1 ≤ n) {μ : Measure (Space n)} (hμ : admissibleMeasure μ) :
    ENNReal.ofReal (((32 / 3 : ℝ) * Real.sqrt 126663739519795200)⁻¹) ≤
      cheegerConstant μ := by
  apply hμ.cheeger_lower_bound_of_uniform_strong_poincare
    (C := (126663739519795200 : ℝ≥0)) (by norm_num)
  intro ν hν _
  exact hν.certified_poincare_mem hn

/-- Both original Cheeger target classes receive the same positive numerical
constant, chosen before dimension and measure. -/
theorem fullCheegerVerification : FullCheegerVerification := by
  apply fullCheegerVerification_of_uniform_strong_poincare
    (C := (126663739519795200 : ℝ≥0)) (by norm_num)
  intro n hn ν hν _
  exact hν.certified_poincare_mem hn

/-- The exact original density-based KLS proposition. -/
theorem klsConjecture : KLSConjecture := by
  obtain ⟨c, hc, _, hfull⟩ := fullCheegerVerification
  exact ⟨c, hc, hfull⟩

end KLS
end

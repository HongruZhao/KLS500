import SpectralReductionCoupledCriterion
import RankFullVerification29
import RefinedIteratedResolventFullCheeger

open MeasureTheory Set
open scoped Topology ContDiff ENNReal NNReal
noncomputable section
namespace KLS

/-- The mixed-rank and variable-block regular criterion gives the same faithful numerical
bound on every law in the original full class. -/
theorem admissibleMeasure.poincareConstant_le_coupledRankYoung
    {n : ℕ} (hn : 1 ≤ n) {μ : Measure (Space n)} (hμ : admissibleMeasure μ) :
    poincareConstant μ ≤ ENNReal.ofReal 500 := by
  have hh := hμ.poincareConstant_le_of_global_regular_bound (by omega)
    (C := (500 : ℝ≥0)) (by norm_num) (fun V κ hprob hV hκ hc hiso => by
      let := hprob
      simpa using ConstantReduction.poincareConstant_le_regular_coupledRankYoung
        (by omega : 0 < n) hV hκ hc hiso)
  simpa using hh

/-- A smaller certified upper bound for the actual universal optimum. -/
theorem universalPoincareConstant_le_coupledRankYoung :
    universalPoincareConstant ≤ ENNReal.ofReal 500 := by
  unfold universalPoincareConstant
  refine iSup_le fun n => iSup_le fun hn => iSup_le fun μ => iSup_le fun hμ => ?_
  exact hμ.poincareConstant_le_coupledRankYoung hn

/-- The improved explicit number belongs to the full faithful constant set. -/
theorem admissibleMeasure.poincare_mem_coupledRankYoung
    {n : ℕ} (hn : 1 ≤ n) {μ : Measure (Space n)} (hμ : admissibleMeasure μ) :
    (500 : ℝ≥0) ∈ poincareConstants μ := by
  have hle := hμ.poincareConstant_le_coupledRankYoung hn
  have hne := poincareConstants_nonempty_iff.mpr (hle.trans_lt ENNReal.ofReal_lt_top)
  apply (poincareConstants_iff_optimal_le hne (hμ.poincareConstant_pos hn)).mpr
  simpa using hle

/-- All original Poincare clauses, including finite-energy integrability,
hold with the improved numerical upper bound for the universal constant. -/
theorem fullPoincareVerification_coupledRankYoung : FullPoincareVerification := by
  have hfinite := universalPoincareConstant_le_coupledRankYoung.trans_lt ENNReal.ofReal_lt_top
  refine ⟨500, by norm_num, universalPoincareConstant_le_coupledRankYoung, hfinite, ?_,
    fullFiniteEnergyPoincare_of_universal_finite hfinite,
    fullL2Poincare_of_universal_finite hfinite⟩
  intro n hn μ hμ
  exact ⟨hμ.one_le_poincareConstant hn, poincareConstant_le_universal hn hμ⟩

/-- Literal real-integral endpoint with every integrability assertion derived
from finite energy on the original class. -/
theorem admissibleMeasure.real_poincare_coupledRankYoung
    {n : ℕ} (hn : 1 ≤ n) {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : LocallyLipschitz f) (he : energy μ f < ⊤) :
    MemLp f 2 μ ∧ Integrable (fun x => ‖gradient f x‖ ^ 2) μ ∧
      ((∫ x, (f x) ^ 2 ∂μ) - (∫ x, f x ∂μ) ^ 2 ≤
        500 * ∫ x, ‖gradient f x‖ ^ 2 ∂μ) := by
  let : IsProbabilityMeasure μ := hμ.isProb
  simpa using finiteEnergy_real_poincare_of_mem_constants hμ.absolutelyContinuousLebesgue
    (hμ.poincare_mem_coupledRankYoung hn) hf he

/-- Explicit original closed-boundary Cheeger endpoint with the improved
Poincare constant and improved analytic conversion. -/
theorem admissibleMeasure.cheeger_lower_coupledRankYoung
    {n : ℕ} (hn : 1 ≤ n) {μ : Measure (Space n)} (hμ : admissibleMeasure μ) :
    ENNReal.ofReal (100 / (223 * Real.sqrt 500)) ≤ cheegerConstant μ := by
  apply hμ.cheeger_lower_bound_refinedIterated_of_uniform_strong_poincare
    (C := (500 : ℝ≥0)) (by norm_num)
  intro ν hν _
  exact hν.poincare_mem_coupledRankYoung hn

/-- Both full original Cheeger classes receive the same improved bound. -/
theorem fullCheegerVerification_coupledRankYoung : FullCheegerVerification := by
  apply fullCheegerVerification_refinedIterated_of_uniform_strong_poincare
    (C := (500 : ℝ≥0)) (by norm_num)
  intro n hn ν hν _
  exact hν.poincare_mem_coupledRankYoung hn

/-- The exact original KLS proposition follows from the new numerical proof. -/
theorem klsConjecture_coupledRankYoung : KLSConjecture := by
  obtain ⟨c, hc, _, hfull⟩ := fullCheegerVerification_coupledRankYoung
  exact ⟨c, hc, hfull⟩

end KLS
end

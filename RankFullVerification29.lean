import SpectralReductionRankCriterion
import OptimizedFullCheeger
import KLS.FaithfulFullTaylorCriterion
import KLS.FullVerification

/-! Third combined improvement. The complete original measure and function
classes are preserved by the accepted strong-density approximation machinery.
All Taylor and seed hypotheses are discharged at the numerical endpoints. -/

open MeasureTheory Set
open scoped Topology ContDiff ENNReal NNReal
noncomputable section
namespace KLS

/-- A regular numerical Poincare bound passes through the actual approximating
laws with the same faithful constant. -/
theorem admissibleMeasure.poincareConstant_le_of_global_regular_bound
    {n : ℕ} (hn : 0 < n) {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {C : ℝ≥0} (hC : 0 < C)
    (hregular : ∀ (V : Space n → ℝ) (κ : ℝ), IsProbabilityMeasure (potentialMeasure V) →
      ContDiff ℝ (⊤ : ℕ∞) V → 0 < κ → StrongConvexOn univ κ V →
      IsIsotropic (potentialMeasure V) → poincareConstant (potentialMeasure V) ≤ (C : ℝ≥0∞)) :
    poincareConstant μ ≤ (C : ℝ≥0∞) := by
  have hmem : C ∈ poincareConstants μ := by
    apply hμ.mem_poincareConstants_of_global_strongDensity hC
    intro ν hν hs
    obtain ⟨V, κ, hV, hκ, hc, heq⟩ := hs
    let : IsProbabilityMeasure (potentialMeasure V) := heq ▸ hν.isProb
    have hiso : IsIsotropic (potentialMeasure V) := heq ▸ hν.isotropic
    have hbound := hregular V κ inferInstance hV hκ hc hiso
    have hne : (poincareConstants (potentialMeasure V)).Nonempty :=
      poincareConstants_nonempty_iff.mpr (hbound.trans_lt ENNReal.coe_lt_top)
    rw [heq]
    apply (poincareConstants_iff_optimal_le hne (hiso.poincareConstant_pos (by omega))).mpr
    exact hbound
  exact poincareConstant_le_of_mem hmem

/-- The rank-sensitive regular criterion gives the same faithful numerical
bound on every law in the original full class. -/
theorem admissibleMeasure.poincareConstant_le_rank29
    {n : ℕ} (hn : 1 ≤ n) {μ : Measure (Space n)} (hμ : admissibleMeasure μ) :
    poincareConstant μ ≤ ENNReal.ofReal 75000 := by
  have hh := hμ.poincareConstant_le_of_global_regular_bound (by omega)
    (C := (75000 : ℝ≥0)) (by norm_num) (fun V κ hprob hV hκ hc hiso => by
      let := hprob
      simpa using ConstantReduction.poincareConstant_le_regular_rankTwentyNine
        (by omega : 0 < n) hV hκ hc hiso)
  simpa using hh

/-- A smaller certified upper bound for the actual universal optimum. -/
theorem universalPoincareConstant_le_rank29 :
    universalPoincareConstant ≤ ENNReal.ofReal 75000 := by
  unfold universalPoincareConstant
  refine iSup_le fun n => iSup_le fun hn => iSup_le fun μ => iSup_le fun hμ => ?_
  exact hμ.poincareConstant_le_rank29 hn

/-- The improved explicit number belongs to the full faithful constant set. -/
theorem admissibleMeasure.poincare_mem_rank29
    {n : ℕ} (hn : 1 ≤ n) {μ : Measure (Space n)} (hμ : admissibleMeasure μ) :
    (75000 : ℝ≥0) ∈ poincareConstants μ := by
  have hle := hμ.poincareConstant_le_rank29 hn
  have hne := poincareConstants_nonempty_iff.mpr (hle.trans_lt ENNReal.ofReal_lt_top)
  apply (poincareConstants_iff_optimal_le hne (hμ.poincareConstant_pos hn)).mpr
  simpa using hle

/-- All original Poincare clauses, including finite-energy integrability,
hold with the improved numerical upper bound for the universal constant. -/
theorem fullPoincareVerification_rank29 : FullPoincareVerification := by
  have hfinite := universalPoincareConstant_le_rank29.trans_lt ENNReal.ofReal_lt_top
  refine ⟨75000, by norm_num, universalPoincareConstant_le_rank29, hfinite, ?_,
    fullFiniteEnergyPoincare_of_universal_finite hfinite,
    fullL2Poincare_of_universal_finite hfinite⟩
  intro n hn μ hμ
  exact ⟨hμ.one_le_poincareConstant hn, poincareConstant_le_universal hn hμ⟩

/-- Literal real-integral endpoint with every integrability assertion derived
from finite energy on the original class. -/
theorem admissibleMeasure.real_poincare_rank29
    {n : ℕ} (hn : 1 ≤ n) {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : LocallyLipschitz f) (he : energy μ f < ⊤) :
    MemLp f 2 μ ∧ Integrable (fun x => ‖gradient f x‖ ^ 2) μ ∧
      ((∫ x, (f x) ^ 2 ∂μ) - (∫ x, f x ∂μ) ^ 2 ≤
        75000 * ∫ x, ‖gradient f x‖ ^ 2 ∂μ) := by
  let : IsProbabilityMeasure μ := hμ.isProb
  simpa using finiteEnergy_real_poincare_of_mem_constants hμ.absolutelyContinuousLebesgue
    (hμ.poincare_mem_rank29 hn) hf he

/-- Explicit original closed-boundary Cheeger endpoint with the improved
Poincare constant and improved analytic conversion. -/
theorem admissibleMeasure.cheeger_lower_rank29
    {n : ℕ} (hn : 1 ≤ n) {μ : Measure (Space n)} (hμ : admissibleMeasure μ) :
    ENNReal.ofReal (5 / (18 * Real.sqrt 75000)) ≤ cheegerConstant μ := by
  apply hμ.cheeger_lower_bound_optimized_of_uniform_strong_poincare
    (C := (75000 : ℝ≥0)) (by norm_num)
  intro ν hν _
  exact hν.poincare_mem_rank29 hn

/-- Both full original Cheeger classes receive the same improved bound. -/
theorem fullCheegerVerification_rank29 : FullCheegerVerification := by
  apply fullCheegerVerification_optimized_of_uniform_strong_poincare
    (C := (75000 : ℝ≥0)) (by norm_num)
  intro n hn ν hν _
  exact hν.poincare_mem_rank29 hn

/-- The exact original KLS proposition follows from the new numerical proof. -/
theorem klsConjecture_rank29 : KLSConjecture := by
  obtain ⟨c, hc, _, hfull⟩ := fullCheegerVerification_rank29
  exact ⟨c, hc, hfull⟩

end KLS
end

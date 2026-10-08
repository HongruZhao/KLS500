import CenteredVarianceCheeger
import OptimizedVarianceGradient
import KLS.FullVerification

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section
namespace KLS

/-- Exact resolvent partitions and centered shell tests give the coefficient
5/18 for the original closed-neighborhood Cheeger constant. -/
theorem admissibleMeasure.cheeger_lower_bound_optimized_of_uniform_strong_poincare
    {n : ℕ} {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {C : ℝ≥0} (hC0 : 0 < (C : ℝ))
    (hstrong : ∀ ν : Measure (Space n), admissibleMeasure ν →
      HasSmoothStronglyConvexDensity ν → C ∈ poincareConstants ν) :
    ENNReal.ofReal (5 / (18 * Real.sqrt C)) ≤ cheegerConstant μ := by
  let : IsProbabilityMeasure μ := hμ.isProb
  have hs : 0 < Real.sqrt (C : ℝ) := Real.sqrt_pos.mpr hC0
  have heq : 5 / (18 * Real.sqrt (C : ℝ)) = ((18/5 : ℝ) * Real.sqrt C)⁻¹ := by
    field_simp
  rw [heq]
  exact centeredVariance_inv_le_cheegerConstant (mul_pos (by norm_num) hs)
    (hμ.boundedVarianceBound_of_uniform_strong_poincare_optimized hC0 hstrong)

/-- The sharper conversion supplies both original full Cheeger measure classes. -/
theorem fullCheegerVerification_optimized_of_uniform_strong_poincare
    {C : ℝ≥0} (hC0 : 0 < (C : ℝ))
    (hstrong : ∀ (n : ℕ), 1 ≤ n → ∀ ν : Measure (Space n),
      admissibleMeasure ν → HasSmoothStronglyConvexDensity ν →
        C ∈ poincareConstants ν) : FullCheegerVerification := by
  refine ⟨5 / (18 * Real.sqrt C), div_pos (by norm_num)
    (mul_pos (by norm_num) (Real.sqrt_pos.mpr hC0)), ?_, ?_⟩
  · intro n hn μ hμ
    exact hμ.cheeger_lower_bound_optimized_of_uniform_strong_poincare hC0 (hstrong n hn)
  · intro n hn μ hμ
    exact hμ.admissibleMeasure.cheeger_lower_bound_optimized_of_uniform_strong_poincare
      hC0 (hstrong n hn)

/-- The accepted universal Poincare bound discharges every input of the new
Cheeger conversion for every original admissible law. -/
theorem admissibleMeasure.certified_cheeger_lower_optimized
    {n : ℕ} (hn : 1 ≤ n) {μ : Measure (Space n)} (hμ : admissibleMeasure μ) :
    ENNReal.ofReal (5 / (18 * Real.sqrt 126663739519795200)) ≤
      cheegerConstant μ := by
  apply hμ.cheeger_lower_bound_optimized_of_uniform_strong_poincare
    (C := (126663739519795200 : ℝ≥0)) (by norm_num)
  intro ν hν _
  exact hν.certified_poincare_mem hn

end KLS
end

import CenteredVarianceCheeger
import EntropyResolventVarianceGradient
import KLS.FullVerification

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section
namespace KLS

/-- Actual finite entropy-resolvent iterations and the accepted centered
shell conversion give Cheeger coefficient1.97 on the original law class. -/
theorem admissibleMeasure.cheeger_lower_bound_entropy_of_uniform_strong_poincare
    {n : ℕ} {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {C : ℝ≥0} (hC0 : 0 < (C : ℝ))
    (hstrong : ∀ ν : Measure (Space n), admissibleMeasure ν →
      HasSmoothStronglyConvexDensity ν → C ∈ poincareConstants ν) :
    ENNReal.ofReal (100/(197*Real.sqrt C)) ≤ cheegerConstant μ := by
  let : IsProbabilityMeasure μ := hμ.isProb
  have hs : 0 < Real.sqrt (C : ℝ) := Real.sqrt_pos.mpr hC0
  have heq : 100/(197*Real.sqrt (C : ℝ))=((197/100 : ℝ)*Real.sqrt C)⁻¹ := by
    field_simp
  rw [heq]
  exact centeredVariance_inv_le_cheegerConstant (mul_pos (by norm_num) hs)
    (hμ.boundedVarianceBound_of_uniform_strong_poincare_entropy hC0 hstrong)

/-- The coefficient1.97 conversion covers both original full Cheeger measure
classes under the same uniform strong-density Poincare premise. -/
theorem fullCheegerVerification_entropy_of_uniform_strong_poincare
    {C : ℝ≥0} (hC0 : 0 < (C : ℝ))
    (hstrong : ∀ (n : ℕ), 1 ≤ n → ∀ ν : Measure (Space n),
      admissibleMeasure ν → HasSmoothStronglyConvexDensity ν →
        C ∈ poincareConstants ν) : FullCheegerVerification := by
  refine ⟨100/(197*Real.sqrt C),div_pos (by norm_num)
    (mul_pos (by norm_num) (Real.sqrt_pos.mpr hC0)),?_,?_⟩
  · intro n hn μ hμ
    exact hμ.cheeger_lower_bound_entropy_of_uniform_strong_poincare hC0 (hstrong n hn)
  · intro n hn μ hμ
    exact hμ.admissibleMeasure.cheeger_lower_bound_entropy_of_uniform_strong_poincare
      hC0 (hstrong n hn)

end KLS
end

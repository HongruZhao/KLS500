import Entropy197500FullVerification

open MeasureTheory
open scoped ENNReal NNReal
noncomputable section
namespace KLS.FinalDustCheegerReview

theorem coefficient_two_comparison :
    (1 : ℝ) / (2 * Real.sqrt 500) ≤ 100 / (197 * Real.sqrt 500) := by
  have hs : 0 < Real.sqrt (500 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith

theorem original_admissible_cheeger_two
    {n : ℕ} (hn : 1 ≤ n) {μ : Measure (Space n)} (hμ : admissibleMeasure μ) :
    ENNReal.ofReal (1 / (2 * Real.sqrt 500)) ≤ cheegerConstant μ := by
  exact (ENNReal.ofReal_le_ofReal coefficient_two_comparison).trans
    (hμ.cheeger_lower_entropy197_500 hn)

theorem original_density_cheeger_two
    {n : ℕ} (hn : 1 ≤ n) {μ : Measure (Space n)} (hμ : IsKLSMeasure μ) :
    ENNReal.ofReal (1 / (2 * Real.sqrt 500)) ≤ cheegerConstant μ := by
  exact original_admissible_cheeger_two hn hμ.admissibleMeasure

theorem exact_openai_poincare500_and_original_cheeger_two :
    (∀ n : ℕ, 1 ≤ n → ∀ ρ : OAI.LeanBlast.KLS.Space n → ℝ,
      OAI.LeanBlast.KLS.IsLogConcaveDensity ρ →
      OAI.LeanBlast.KLS.IsIsotropic (OAI.LeanBlast.KLS.densityMeasure ρ) →
      OAI.LeanBlast.KLS.PoincareBound (OAI.LeanBlast.KLS.densityMeasure ρ) 500) ∧
    (∀ n : ℕ, 1 ≤ n → ∀ μ : Measure (Space n), admissibleMeasure μ →
      ENNReal.ofReal (1 / (2 * Real.sqrt 500)) ≤ cheegerConstant μ) := by
  exact ⟨OAI.LeanBlast.KLS.poincareBound500,
    fun _ hn _ hμ => original_admissible_cheeger_two hn hμ⟩

end KLS.FinalDustCheegerReview
end

#check KLS.FinalDustCheegerReview.coefficient_two_comparison
#print axioms KLS.FinalDustCheegerReview.coefficient_two_comparison
#check KLS.FinalDustCheegerReview.original_admissible_cheeger_two
#print axioms KLS.FinalDustCheegerReview.original_admissible_cheeger_two
#check KLS.FinalDustCheegerReview.original_density_cheeger_two
#print axioms KLS.FinalDustCheegerReview.original_density_cheeger_two
#check KLS.FinalDustCheegerReview.exact_openai_poincare500_and_original_cheeger_two
#print axioms KLS.FinalDustCheegerReview.exact_openai_poincare500_and_original_cheeger_two

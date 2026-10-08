import CheegerTwoReverification

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

/- Final public endpoints, using the unchanged upstream OpenAI model. -/
namespace KLS.Final

theorem openaiKLS : OAI.LeanBlast.KLS.KLSStatement :=
  KLS.exactOpenAIKLSStatement_entropy197_500

theorem openaiPoincare500 :
    ∀ n : ℕ, 1 ≤ n → ∀ ρ : OAI.LeanBlast.KLS.Space n → ℝ,
      OAI.LeanBlast.KLS.IsLogConcaveDensity ρ →
      OAI.LeanBlast.KLS.IsIsotropic (OAI.LeanBlast.KLS.densityMeasure ρ) →
      OAI.LeanBlast.KLS.PoincareBound (OAI.LeanBlast.KLS.densityMeasure ρ) 500 :=
  OAI.LeanBlast.KLS.poincareBound500

theorem cheegerTwo {n : ℕ} (hn : 1 ≤ n)
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ) :
    ENNReal.ofReal (1 / (2 * Real.sqrt 500)) ≤ cheegerConstant μ :=
  FinalDustCheegerReview.original_admissible_cheeger_two hn hμ

theorem cheeger197 {n : ℕ} (hn : 1 ≤ n)
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ) :
    ENNReal.ofReal (100 / (197 * Real.sqrt 500)) ≤ cheegerConstant μ :=
  hμ.cheeger_lower_entropy197_500 hn

/-- Both numerical bounds for each density in the exact upstream law class. -/
theorem openaiDensityBounds {n : ℕ} (hn : 1 ≤ n)
    {ρ : OAI.LeanBlast.KLS.Space n → ℝ}
    (hρ : OAI.LeanBlast.KLS.IsLogConcaveDensity ρ)
    (hiso : OAI.LeanBlast.KLS.IsIsotropic (OAI.LeanBlast.KLS.densityMeasure ρ)) :
    OAI.LeanBlast.KLS.PoincareBound (OAI.LeanBlast.KLS.densityMeasure ρ) 500 ∧
      ENNReal.ofReal (1 / (2 * Real.sqrt 500)) ≤
        cheegerConstant (OAI.LeanBlast.KLS.densityMeasure ρ) := by
  exact ⟨openaiPoincare500 n hn ρ hρ hiso,
    cheegerTwo hn (OpenAIBridge.admissible hρ hiso)⟩

end KLS.Final

end

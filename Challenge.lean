import FinalKLSRange

/-!
# KLS endpoint statements

This interface was written after the verified development. Its theorem statements
use the original definitions and have proofs through the accepted endpoint modules.
It is not an independent pre-solution specification. The solution entry point
`KLS500.lean` does not import this file; the two modules are checked separately.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace KLS500

/-- Poincare bound on every original admissible law and every locally Lipschitz
L2 test function. Variance and energy are the original extended-real quantities. -/
theorem poincare500 {n : ℕ} (hn : 1 ≤ n)
    {μ : Measure (KLS.Space n)} (hμ : KLS.admissibleMeasure μ)
    {f : KLS.Space n → ℝ} (hf : KLS.LocallyLipschitzTests μ f) :
    KLS.variance μ f ≤ ENNReal.ofReal 500 * KLS.energy μ f := by
  simpa using hμ.poincare_mem_coupledRankYoung hn f hf

/-- The improved bound for the original closed-neighborhood Cheeger constant.
The denominator factor is 197/100 = 1.97. -/
theorem cheeger197 {n : ℕ} (hn : 1 ≤ n)
    {μ : Measure (KLS.Space n)} (hμ : KLS.admissibleMeasure μ) :
    ENNReal.ofReal (100 / (197 * Real.sqrt 500)) ≤ KLS.cheegerConstant μ :=
  KLS.Final.cheeger197 hn hμ

/-- The optimum over all dimensions and admissible laws lies in [4, 500].
The lower bound concerns this supremum, not each individual law. -/
theorem universalPoincareRange :
    (4 : ℝ≥0∞) ≤ KLS.universalPoincareConstant ∧
      KLS.universalPoincareConstant ≤ ENNReal.ofReal 500 :=
  KLS.Final.universalPoincareRange

/-- Fixed witness 500 in the unchanged upstream OpenAI density formulation. -/
theorem openaiPoincare500 :
    ∀ n : ℕ, 1 ≤ n → ∀ ρ : OAI.LeanBlast.KLS.Space n → ℝ,
      OAI.LeanBlast.KLS.IsLogConcaveDensity ρ →
      OAI.LeanBlast.KLS.IsIsotropic (OAI.LeanBlast.KLS.densityMeasure ρ) →
      OAI.LeanBlast.KLS.PoincareBound (OAI.LeanBlast.KLS.densityMeasure ρ) 500 :=
  KLS.Final.openaiPoincare500

/-- The exact upstream OpenAI existential KLS statement. -/
theorem openaiKLS : OAI.LeanBlast.KLS.KLSStatement := KLS.Final.openaiKLS

end KLS500

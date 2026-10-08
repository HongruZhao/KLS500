import FinalKLS500
import KLS.ExponentialFullClass

open scoped ENNReal NNReal

noncomputable section

namespace KLS.Final

/-- The best universal Poincare constant lies between 4 and 500. The lower
bound comes from the centered unit exponential law; it is not a lower bound
of 4 for every admissible measure. -/
theorem universalPoincareRange :
    (4 : ℝ≥0∞) ≤ KLS.universalPoincareConstant ∧
      KLS.universalPoincareConstant ≤ ENNReal.ofReal 500 :=
  ⟨KLS.four_le_universalPoincareConstant,
    KLS.universalPoincareConstant_le_coupledRankYoung⟩

/-- Poincare KLS in the exact unchanged upstream OpenAI formulation. -/
theorem poincareKLS : OAI.LeanBlast.KLS.KLSStatement := openaiKLS

/-- Cheeger KLS in the original density-based, closed-neighborhood formulation. -/
theorem cheegerKLS : KLS.KLSConjecture := KLS.klsConjecture_entropy197_500

/-- Cheeger KLS on both the original density and full compact-set law classes. -/
theorem fullCheegerKLS : KLS.FullCheegerVerification :=
  KLS.fullCheegerVerification_entropy197_500

end KLS.Final

end

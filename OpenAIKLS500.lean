import OpenAIKLSBridge
import CoupledRankYoungFullVerification

/-! The exact upstream OpenAI dimension-free statement, with our proved
numerical witness 500. The upstream model and its definitions are unchanged. -/
open MeasureTheory
noncomputable section
namespace OAI.LeanBlast.KLS

theorem poincareBound500 : ∀ n : ℕ, 1 ≤ n →
    ∀ ρ : Space n → ℝ, IsLogConcaveDensity ρ → IsIsotropic (densityMeasure ρ) →
      PoincareBound (densityMeasure ρ) 500 := by
  intro n hn ρ hρ hiso
  exact _root_.KLS.OpenAIBridge.poincareBound_of_mem hρ
    ((_root_.KLS.OpenAIBridge.admissible hρ hiso).poincare_mem_coupledRankYoung hn)

theorem klsStatement500 : KLSStatement := by
  exact ⟨500, by norm_num, poincareBound500⟩

theorem fullStatement500 : FullStatement := klsStatement500

end OAI.LeanBlast.KLS
end

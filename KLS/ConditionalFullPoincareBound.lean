import KLS.WeightedTaylorGrowth288
import KLS.FaithfulFullTaylorCriterion

/-! A concrete sufficient full-class Poincare constant, conditional on the
literal compact localization matrix seed and the actual base process bound.
The full locally Lipschitz test class and actual law approximations are those
of the independently proved FaithfulFullTaylorCriterion. -/
open MeasureTheory Set Matrix
open scoped ENNReal BigOperators
noncomputable section
namespace KLS
open AdaptiveLocalization

theorem admissibleMeasure.poincareConstant_le_of_uniform_seed_and_base
    (hseed : ∀ n, UniformCompactMatrixSeed n)
    (hbase : ∀ n, CompactProcessEnergyBound n 1 (cumulantEnergyMajorant 144 1))
    {n : ℕ} (hn : 0 < n) {μ : Measure (Space n)} (hμ : admissibleMeasure μ) :
    poincareConstant μ ≤ ENNReal.ofReal 126663739519795200 := by
  have hTaylor : ∀ (V : Space n → ℝ) (κ : ℝ), IsProbabilityMeasure (potentialMeasure V) →
      ContDiff ℝ (⊤ : ℕ∞) V → 0 < κ → StrongConvexOn univ κ V →
      IsIsotropic (potentialMeasure V) → WeightedCoordinateTaylorBound V (Real.sqrt 288) := by
    intro V κ hprob hV hκ hc hiso
    let := hprob
    exact weightedCoordinateTaylorBound_sqrt288_of_seed_and_base hseed hbase
      (hV.of_le (by simp)) hiso hκ (coordinateHessian_lower_of_strongConvexOn (hV.of_le (by simp)) hc)
  have hh := hμ.poincareConstant_le_of_global_regular_Taylor hn one_le_sqrt288 hTaylor
  convert hh using 1
  norm_num [Real.sq_sqrt]

theorem universalPoincareConstant_le_of_uniform_seed_and_base
    (hseed : ∀ n, UniformCompactMatrixSeed n)
    (hbase : ∀ n, CompactProcessEnergyBound n 1 (cumulantEnergyMajorant 144 1)) :
    universalPoincareConstant ≤ ENNReal.ofReal 126663739519795200 := by
  unfold universalPoincareConstant
  refine iSup_le fun n => iSup_le fun hn => iSup_le fun μ => iSup_le fun hμ => ?_
  exact hμ.poincareConstant_le_of_uniform_seed_and_base hseed hbase (by omega)

theorem universalPoincareConstant_lt_top_of_uniform_seed_and_base
    (hseed : ∀ n, UniformCompactMatrixSeed n)
    (hbase : ∀ n, CompactProcessEnergyBound n 1 (cumulantEnergyMajorant 144 1)) :
    universalPoincareConstant < ⊤ :=
  (universalPoincareConstant_le_of_uniform_seed_and_base hseed hbase).trans_lt ENNReal.ofReal_lt_top

end KLS
end

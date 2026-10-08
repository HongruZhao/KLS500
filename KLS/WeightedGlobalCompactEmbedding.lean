import KLS.WeightedCutoffApproximation
import KLS.WeightedCompactEmbedding

/-! Compactness of the actual full weighted energy inclusion, by actual tails. -/
open MeasureTheory Matrix Filter
open scoped ContDiff Topology
noncomputable section
namespace KLS
variable {n : ℕ}

theorem weightedH1SquareCutoff_isCompactOperator {φ : Space n → ℝ}
    (hφ : Continuous φ) (k : ℕ) :
    IsCompactOperator (weightedH1SquareCutoff hφ k) := by
  exact (weightedH1CompactValue_isCompactOperator hφ (smoothCutoff_contDiff k)
    (smoothCutoff_hasCompactSupport k)).clm_comp
      (volumeL2CompactToWeighted hφ (smoothCutoff_contDiff k).continuous
        (smoothCutoff_hasCompactSupport k))

/-- The graph inclusion is compact under actual positive Hessian confinement.
The curvature lower bound may depend on the potential. No universal gap is assumed. -/
theorem weightedH1Value_isCompactOperator {φ : Space n → ℝ} {κ : ℝ}
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ y (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ y *ᵥ a)) :
    IsCompactOperator (weightedH1Value φ) := by
  exact isCompactOperator_of_tendsto (weightedH1SquareCutoff_tendsto hφ hκ hlower)
    (Eventually.of_forall (weightedH1SquareCutoff_isCompactOperator hφ.continuous))

end KLS
end
#print axioms KLS.weightedH1SquareCutoff_isCompactOperator
#print axioms KLS.weightedH1Value_isCompactOperator

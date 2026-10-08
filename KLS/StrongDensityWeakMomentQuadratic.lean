import KLS.WeakMomentQuadratic
import KLS.BoundedMomentMapExistence
import KLS.StrongBoundedDensityApproximation
import Mathlib.Analysis.Convex.Measure

open MeasureTheory ProbabilityTheory Matrix Set Filter
open scoped ContDiff NNReal ENNReal
noncomputable section
namespace KLS
variable {n : ℕ}

/-- Replacing a convex target by its closure preserves its potential law. -/
theorem potentialMeasure_restrict_closure_of_convex
    (V : Space n → ℝ) {K : Set (Space n)} (hK : Convex ℝ K) :
    (potentialMeasure V).restrict (closure K) = (potentialMeasure V).restrict K := by
  have hac : potentialMeasure V ≪ volume := withDensity_absolutelyContinuous _ _
  exact Measure.restrict_congr_set
    ((closure_ae_eq_of_null_frontier (hK.addHaar_frontier volume)).filter_mono hac.ae_le)

/-- Actual bounded moment existence discharges the weak source premise
 for the exact smooth bounded uniformly convex target approximation class. -/
theorem admissibleMeasure.quadraticVarianceEight_of_actual_strongDensity
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (hreg : HasSmoothBoundedStronglyConvexDensity μ) : QuadraticVarianceEight μ := by
  let : IsProbabilityMeasure μ := hμ.isProb
  have hcompact := hreg.to_smoothBoundedConvexDensity.isCompact_support
  obtain ⟨K, V, κ, hKo, hKc, hKb, _, hV, hκ, hstrong, htarget⟩ := hreg
  obtain ⟨R, hR, hbound⟩ := hKb.exists_pos_norm_le
  let L : ℝ≥0 := ⟨R, hR.le⟩
  have hbounded : ∀ᵐ y ∂μ, ‖y‖ ≤ L := by
    rw [htarget]
    exact (ae_restrict_mem hKo.measurableSet).mono fun y hy => hbound y hy
  obtain ⟨u, hLip, hc, hprob, hmap⟩ := hμ.isotropic.exists_bounded_momentMap L hbounded
  let : IsProbabilityMeasure (potentialMeasure u) := hprob
  have hpush : MomentMap.gradientPushforward u = μ := hmap
  have hclosedTarget : μ = (potentialMeasure V).restrict (closure K) :=
    htarget.trans (potentialMeasure_restrict_closure_of_convex V hKc).symm
  have hVc : ConvexOn ℝ univ V := convexOn_of_strongConvexOn_nonneg hκ.le hstrong
  rw [strongConvexOn_iff_convex] at hstrong
  exact quadraticVarianceEight_of_weak_uniform_momentMap hμ hcompact hLip hc
    (hV.of_le (by simp)) hVc hκ hstrong isClosed_closure hKc.closure hclosedTarget hpush

end KLS
end

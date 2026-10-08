import KLS.VarianceGradientLawApproximation

open MeasureTheory Set Filter
open scoped Topology ContDiff ENNReal NNReal

noncomputable section
namespace KLS
variable {n : ℕ}

/-- The actual smooth-class resolvent theorem supplies the smooth variance
criterion from a faithful Poincare bound on a strongly convex density. -/
theorem smoothVarianceBound_of_strongDensity_poincare
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hdensity : HasSmoothStronglyConvexDensity μ)
    {C : ℝ≥0} (hC : C ∈ poincareConstants μ) (hC0 : 0 < (C : ℝ)) :
    SmoothCompactVarianceGradientBound μ ((16 / 3 : ℝ) * Real.sqrt C) := by
  obtain ⟨V, κ, hV, hκ, hstrong, heq⟩ := hdensity
  subst μ
  intro f hf hc B hB hfB
  have hb := variance_le_gradient_L1_of_poincare_smooth_compact hV
    (convexOn_of_strongConvexOn_nonneg hκ.le hstrong) hC hC0 hf hc hB hfB
  calc
    ProbabilityTheory.variance f (potentialMeasure V) ≤
        (16 / 3 : ℝ) * B * Real.sqrt C *
          (∫ x, ‖gradient f x‖ ∂potentialMeasure V) := hb
    _ = ((16 / 3 : ℝ) * Real.sqrt C) * B *
        (∫ x, ‖gradient f x‖ ∂potentialMeasure V) := by ring

/-- A single faithful Poincare constant for the smooth strongly convex
admissible subclass gives the actual bounded variance estimate on the full
original admissible class. The uniform Poincare premise remains explicit. -/
theorem admissibleMeasure.boundedVarianceBound_of_uniform_strong_poincare
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {C : ℝ≥0} (hC0 : 0 < (C : ℝ))
    (hstrong : ∀ ν : Measure (Space n), admissibleMeasure ν →
      HasSmoothStronglyConvexDensity ν → C ∈ poincareConstants ν) :
    BoundedVarianceGradientBound μ ((16 / 3 : ℝ) * Real.sqrt C) := by
  apply hμ.boundedVarianceBound_of_global_strongDensity
  intro ν hν hdensity
  let : IsProbabilityMeasure ν := hν.isProb
  exact smoothVarianceBound_of_strongDensity_poincare hdensity
    (hstrong ν hν hdensity) hC0

end KLS
end

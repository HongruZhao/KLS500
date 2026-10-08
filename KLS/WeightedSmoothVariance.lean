import KLS.WeightedWeakLiouville
import KLS.BrascampLiebFiniteEnergy
import KLS.GradientDualVariance

/-!
# Smooth full-space variance bounds with proved range density

The actual weak Liouville theorem removes the range-density premise from
the existing variational reductions. Probability normalization, genuine
test-function integrability, and the stated Hessian or dual-energy
hypotheses remain explicit. No approximation of nonsmooth potentials or
arbitrary convex supports is asserted here.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ContDiff

noncomputable section
namespace KLS
variable {n : ℕ}

theorem brascampLieb_variance_smooth_compact {φ f : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hf : ContDiff ℝ 1 f)
    (hpos : ∀ x, (coordinateHessian φ x).PosDef) (hc : HasCompactSupport f) :
    ProbabilityTheory.variance f (potentialMeasure φ) ≤
      ∫ x, inverseHessianGradientForm φ f x ∂potentialMeasure φ :=
  brascampLieb_variance_of_diffusionRangeDense hφ hf hpos hc (diffusionRangeDense_of_contDiff hφ)

theorem brascampLieb_variance_smooth_of_integrable_energy {φ f : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hf : ContDiff ℝ 1 f)
    (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    (hf2 : MemLp f 2 (potentialMeasure φ))
    (hinv : Integrable (inverseHessianGradientForm φ f) (potentialMeasure φ)) :
    ProbabilityTheory.variance f (potentialMeasure φ) ≤
      ∫ x, inverseHessianGradientForm φ f x ∂potentialMeasure φ :=
  brascampLieb_variance_of_integrable_energy hφ hf hpos hf2 hinv (diffusionRangeDense_of_contDiff hφ)

theorem variance_le_sum_gradient_dual_smooth {φ f : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)] {K : Fin n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hconv : ConvexOn ℝ univ φ)
    (hf : ContDiff ℝ 1 f) (hf2 : MemLp f 2 (potentialMeasure φ))
    (hK : ∀ i, 0 ≤ K i) (hdual : ∀ i, CoordinateGradientDualBound φ f i (K i)) :
    ProbabilityTheory.variance f (potentialMeasure φ) ≤ ∑ i, K i :=
  variance_le_sum_gradient_dual_of_rangeDense hφ hconv hf hf2 hK hdual (diffusionRangeDense_of_contDiff hφ)

end KLS
end

#print axioms KLS.brascampLieb_variance_smooth_compact
#print axioms KLS.brascampLieb_variance_smooth_of_integrable_energy
#print axioms KLS.variance_le_sum_gradient_dual_smooth

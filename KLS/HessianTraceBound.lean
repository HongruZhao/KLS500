import KLS.HessianEntryBrascampLieb
import KLS.HessianTraceEnergyComparison
import KLS.WeightedWeakLiouville
import KLS.HessianPotentialDrift

/-!
# The factor-two Hessian trace bound under explicit analytic hypotheses

The actual pointwise evolution, its L¹-drift integration, the inverse-metric
tensor comparison, the isotropic Hessian mean and summed scalar
Brascamp–Lieb bounds now compose. The proved weak Liouville theorem supplies
diffusion-range density. Moment-map existence/regularity remains separate.
-/

open Matrix InnerProductSpace MeasureTheory Set
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section
namespace KLS

variable {n : ℕ}

theorem integral_hessianTraceSquare_le_two_trace {φ V : Space n → ℝ}
    (hφ : ContDiff ℝ 4 φ) (hV : ContDiff ℝ 2 V)
    (hφconv : ConvexOn ℝ univ φ) (hVconv : ConvexOn ℝ univ V)
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    (hMA : ∀ x, Real.log (coordinateHessian φ x).det = -φ x + V (gradient φ x))
    (hLφ : Integrable (hessianMetricDiffusion φ V φ) (potentialMeasure φ))
    (hH : Bornology.IsBounded (range (coordinateHessian φ)))
    (hiso : IsIsotropic (MomentMap.gradientPushforward φ))
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.PosSemidef) :
    (∫ x, hessianTraceSquare φ B x ∂potentialMeasure φ) ≤ 2 * (B * B).trace := by
  obtain ⟨_, hA, _, _, _⟩ := hessianTrace_moment_identity_of_integrable_drift
    hφ hV hφconv hVconv hpos hMA hLφ hH hB
  have hv := hessianTrace_variance_control hφ hpos hH hiso hB hA
    (diffusionRangeDense_of_contDiff (hφ.of_le (by norm_num)))
  have he := integral_hessianTraceGradientTerm_le_half_square
    hφ hV hφconv hVconv hpos hMA hLφ hH hB
  linarith

/-- Linear target-gradient growth and actual isotropy discharge the remaining
potential-drift integrability condition. No range-density or L¹-drift premise remains. -/
theorem integral_hessianTraceSquare_le_two_trace_of_linear_growth {φ V : Space n → ℝ}
    (hφ : ContDiff ℝ 4 φ) (hV : ContDiff ℝ 2 V)
    (hφconv : ConvexOn ℝ univ φ) (hVconv : ConvexOn ℝ univ V)
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    (hMA : ∀ x, Real.log (coordinateHessian φ x).det = -φ x + V (gradient φ x))
    (hH : Bornology.IsBounded (range (coordinateHessian φ)))
    (hiso : IsIsotropic (MomentMap.gradientPushforward φ))
    {a b : ℝ} (hgrowth : ∀ y, ‖gradient V y‖ ≤ a + b * ‖y‖)
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.PosSemidef) :
    (∫ x, hessianTraceSquare φ B x ∂potentialMeasure φ) ≤ 2 * (B * B).trace := by
  exact integral_hessianTraceSquare_le_two_trace hφ hV hφconv hVconv hpos hMA
    (integrable_hessianMetricDiffusion_potential_of_linear_growth
      (hφ.of_le (by norm_num)) hpos hiso hgrowth) hH hiso hB

end KLS
end

#print axioms KLS.integral_hessianTraceSquare_le_two_trace

#print axioms KLS.integral_hessianTraceSquare_le_two_trace_of_linear_growth

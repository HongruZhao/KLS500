import KLS.HessianTraceBound

/-!
# The trace bound for bounded gradient image

This supplies the drift integrability from the original bounded-target
moment-map hypotheses. It does not identify that bounded target with a
globally positive density on all of Euclidean space.
-/

open MeasureTheory InnerProductSpace Matrix Set Filter
open scoped ContDiff Matrix.Norms.Elementwise
noncomputable section
namespace KLS
variable {n : ℕ}

theorem integrable_hessianMetricDiffusion_potential_of_bounded_gradient
    {φ V : Space n → ℝ} [IsFiniteMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 4 φ) (hV : ContDiff ℝ 2 V)
    (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    (hgrad : Bornology.IsBounded (range (gradient φ))) :
    Integrable (hessianMetricDiffusion φ V φ) (potentialMeasure φ) := by
  obtain ⟨D, _, hD⟩ := exists_bound_diffusion_potentialHeight hφ hV hpos hgrad (0 : Space n)
  apply (integrable_const D).mono'
    (continuous_hessianMetricDiffusion hφ hV (hφ.of_le (by norm_num)) hpos).aestronglyMeasurable
  exact Eventually.of_forall fun x => by
    simpa only [hessianMetricDiffusion_potentialHeight_eq] using hD x

theorem integral_hessianTraceSquare_le_two_trace_of_bounded_gradient
    {φ V : Space n → ℝ}
    (hφ : ContDiff ℝ 4 φ) (hV : ContDiff ℝ 2 V)
    (hφconv : ConvexOn ℝ univ φ) (hVconv : ConvexOn ℝ univ V)
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    (hMA : ∀ x, Real.log (coordinateHessian φ x).det = -φ x + V (gradient φ x))
    (hH : Bornology.IsBounded (range (coordinateHessian φ)))
    (hgrad : Bornology.IsBounded (range (gradient φ)))
    (hiso : IsIsotropic (MomentMap.gradientPushforward φ))
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.PosSemidef) :
    (∫ x, hessianTraceSquare φ B x ∂potentialMeasure φ) ≤ 2 * (B * B).trace :=
  integral_hessianTraceSquare_le_two_trace hφ hV hφconv hVconv hpos hMA
    (integrable_hessianMetricDiffusion_potential_of_bounded_gradient hφ hV hpos hgrad)
    hH hiso hB

end KLS
end

#print axioms KLS.integrable_hessianMetricDiffusion_potential_of_bounded_gradient
#print axioms KLS.integral_hessianTraceSquare_le_two_trace_of_bounded_gradient

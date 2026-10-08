import KLS.MomentRescalingData

open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff NNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

/-- Exact weak transport under the actual quadratic normalization. The
source and target weights are both transformed with the exact Jacobian. -/
theorem weighted_quadratic_rescaling_transport
    {u W V : Space n → ℝ} (hu : Differentiable ℝ u) (hW : Measurable W) (hV : Measurable V)
    {K : Set (Space n)}
    (hpush : (potentialMeasure W).map (gradient u) = (potentialMeasure V).restrict K)
    (x₀ p : Space n) (a : ℝ) {r : ℝ} (hr : r ≠ 0) :
    (potentialMeasure (scalarNormalizedPotential W x₀ r)).map
      (gradient (quadraticallyRescaledPotential u x₀ p a r)) =
        (potentialMeasure (scalarNormalizedPotential V p r)).restrict
          ((scalarNormalizationEquiv p r hr) '' K) := by
  rw [← map_potentialMeasure_scalarNormalization hW x₀ hr,
    Measure.map_map (measurable_gradient _) (scalarNormalizationEquiv x₀ r hr).continuous.measurable,
    gradient_rescaling_comp_normalization hu x₀ p a hr,
    ← Measure.map_map (scalarNormalizationEquiv p r hr).continuous.measurable (measurable_gradient u)]
  rw [hpush, map_restrict_scalarNormalization, map_potentialMeasure_scalarNormalization hV]

/-- The Jacobian constants cancel in the actual rescaled Monge-Ampere
density. It is exactly the original density at the rescaled spatial point. -/
theorem weighted_quadratic_rescaling_density_identity
    {u W V : Space n → ℝ} (hu : Differentiable ℝ u)
    (x₀ p : Space n) (a : ℝ) {r : ℝ} (hr : r ≠ 0) (y : Space n) :
    Real.exp (-scalarNormalizedPotential W x₀ r y + scalarNormalizedPotential V p r
      (gradient (quadraticallyRescaledPotential u x₀ p a r) y)) =
      Real.exp (-W (x₀ + r • y) + V (gradient u (x₀ + r • y))) := by
  rw [gradient_quadraticallyRescaledPotential hu x₀ p a hr]
  simp only [scalarNormalizedPotential, smul_smul, mul_inv_cancel₀ hr, one_smul]
  have he (z : Space n) : p + (z - p) = z := by abel
  rw [he]
  congr 1
  ring

end KLS
end

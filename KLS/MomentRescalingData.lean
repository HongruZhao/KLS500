import KLS.RescaledMomentRegularity

open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff NNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

lemma exists_lipschitzWith_quadraticallyRescaledPotential
    {u : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (x₀ p : Space n) (a r : ℝ) :
    ∃ D : ℝ≥0, LipschitzWith D (quadraticallyRescaledPotential u x₀ p a r) := by
  have hi := (isometry_add_left x₀).lipschitzWith.comp
    (r • ContinuousLinearMap.id ℝ (Space n)).lipschitzWith
  have hnum := ((hLip.comp hi).sub (LipschitzWith.const a)).sub (r • innerSL ℝ p).lipschitzWith
  have hh := ((r ^ 2)⁻¹ • ContinuousLinearMap.id ℝ ℝ).lipschitzWith.comp hnum
  refine ⟨‖(r ^ 2)⁻¹ • ContinuousLinearMap.id ℝ ℝ‖₊ *
    (L * (1 * ‖r • ContinuousLinearMap.id ℝ (Space n)‖₊) + 0 + ‖r • innerSL ℝ p‖₊), ?_⟩
  convert hh using 1
  funext y
  simp only [Function.comp_apply, ContinuousLinearMap.id_apply, _root_.smul_apply,
    innerSL_apply_apply, smul_eq_mul, quadraticallyRescaledPotential]
  ring

/-- Original finite-mass weak moment data give an actual normalized potential
with C1 regularity and strict convexity, and the exact transformed weak
transport equation with its explicit source weight. -/
theorem moment_quadratic_rescaling_data
    {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : Continuous V) [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    (x₀ p : Space n) (a : ℝ) {r : ℝ} (hr : r ≠ 0) :
    (∃ D : ℝ≥0, LipschitzWith D (quadraticallyRescaledPotential u x₀ p a r)) ∧
      ContDiff ℝ 1 (quadraticallyRescaledPotential u x₀ p a r) ∧
      StrictConvexOn ℝ univ (quadraticallyRescaledPotential u x₀ p a r) ∧
      Continuous (scalarNormalizedPotential u x₀ r) ∧
      IsFiniteMeasure (potentialMeasure (scalarNormalizedPotential u x₀ r)) ∧
      Continuous (scalarNormalizedPotential V p r) ∧
      IsClosed ((scalarNormalizationEquiv p r hr) '' K) ∧
      Convex ℝ ((scalarNormalizationEquiv p r hr) '' K) ∧
      (potentialMeasure (scalarNormalizedPotential u x₀ r)).map
        (gradient (quadraticallyRescaledPotential u x₀ p a r)) =
          (potentialMeasure (scalarNormalizedPotential V p r)).restrict
            ((scalarNormalizationEquiv p r hr) '' K) := by
  have hu := moment_contDiff_one_closedTarget hLip hc hV hK hKc hpush
  have hs := moment_strictConvexOn hLip hc hV hK.measurableSet hKc hpush
  exact ⟨exists_lipschitzWith_quadraticallyRescaledPotential hLip x₀ p a r,
    contDiff_quadraticallyRescaledPotential hu x₀ p a r,
    strictConvexOn_quadraticallyRescaledPotential hs x₀ p a hr,
    continuous_scalarNormalizedPotential hLip.continuous x₀ r,
    isFiniteMeasure_scalarNormalizedPotential hLip.continuous.measurable x₀ hr,
    continuous_scalarNormalizedPotential hV p r,
    isClosed_scalarNormalization_image hK p hr, convex_scalarNormalization_image hKc p hr,
    moment_quadratic_rescaling_transport (hu.differentiable (by norm_num)) hV.measurable hpush x₀ p a hr⟩

end KLS
end

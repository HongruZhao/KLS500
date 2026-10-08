import KLS.CompactKernelSmoothing
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Actual derivative of a smooth compact-source convolution

The derivative is passed through the integral using a uniform bound on the
actual derivative over a compact set of translates of the source support.
-/

open MeasureTheory Set Filter Metric
open scoped ContDiff Topology Pointwise

noncomputable section
namespace KLS

theorem hasFDerivAt_integral_translate_of_compact_support {n : ℕ}
    {μ : Measure (Space n)} [IsFiniteMeasure μ] (hμ : IsCompact μ.support)
    {g : Space n → ℝ} (hg : ContDiff ℝ 1 g) (x : Space n) :
    HasFDerivAt (fun z => ∫ y, g (z - y) ∂μ)
      (∫ y, fderiv ℝ g (x - y) ∂μ) x := by
  let K : Set (Space n) :=
    (fun p : Space n × Space n => p.1 - p.2) '' (closedBall x 1 ×ˢ μ.support)
  have hK : IsCompact K := ((isCompact_closedBall x 1).prod hμ).image (by fun_prop)
  have hD : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by norm_num)
  obtain ⟨C, hC⟩ := (hK.image hD).isBounded.exists_norm_le
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := ball x 1) (F' := fun z y => fderiv ℝ g (z - y))
    (bound := fun _ => C) (ball_mem_nhds x zero_lt_one)
  · exact Eventually.of_forall fun z =>
      (hg.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · exact integrable_of_continuous_compact_support_measure hμ
      (hg.continuous.comp (continuous_const.sub continuous_id))
  · exact (hD.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · filter_upwards [μ.support_mem_ae] with y hy z hz
    exact hC _ ⟨z - y, ⟨(z, y), ⟨ball_subset_closedBall hz, hy⟩, rfl⟩, rfl⟩
  · exact integrable_const C
  · apply Eventually.of_forall
    intro y z _
    simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_id] using (hg.differentiable (by norm_num) (z - y)).hasFDerivAt.comp z
      ((hasFDerivAt_id z).sub_const y)

end KLS
end

#print axioms KLS.hasFDerivAt_integral_translate_of_compact_support

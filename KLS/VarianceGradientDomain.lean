import KLS.VarianceGradientCriteria

open MeasureTheory Set Filter
open scoped Topology ContDiff ENNReal NNReal

noncomputable section
namespace KLS
variable {n : ℕ}

/-- Genuine compact mollifiers extend a smooth variance criterion to compact
locally Lipschitz tests, preserving the original uniform value bound. -/
theorem variance_le_gradient_L1_of_smooth_compact_variance_bound
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : μ ≪ volume)
    {K : ℝ} (hbound : SmoothCompactVarianceGradientBound μ K)
    {f : Space n → ℝ} (hf : LocallyLipschitz f) (hfc : HasCompactSupport f)
    {B : ℝ} (hB : 0 ≤ B) (hfB : ∀ x, |f x| ≤ B) :
    ProbabilityTheory.variance f μ ≤ K * B * (∫ x, ‖gradient f x‖ ∂μ) := by
  have hs := compact_locallyLipschitz_absolutelyContinuous_smoothing hμ hf hfc
  have hf2 : MemLp f 2 μ := MemLp.of_bound
    hf.continuous.aestronglyMeasurable B (Eventually.of_forall hfB)
  have hvar := variance_tendsto_of_eLpNorm_sub_tendsto_zero
    (fun k => (hs.1 k).2.2.1) hf2 hs.2.1
  have hgrad := integral_norm_gradient_mollify_tendsto hμ hf hfc
  apply le_of_tendsto_of_tendsto hvar (hgrad.const_mul (K * B))
  apply Eventually.of_forall
  intro k
  apply hbound (mollify k f) (mollify_contDiff hf.continuous.locallyIntegrable k)
    (hasCompactSupport_mollify hfc k) B hB
  intro x
  exact norm_mollify_le_of_ae_bound (Eventually.of_forall hfB) k x

/-- Actual spatial cutoffs and actual mollifiers prove the full bounded-test
criterion from its smooth compact restriction for an absolutely continuous law. -/
theorem boundedVarianceGradientBound_of_smooth_compact
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : μ ≪ volume)
    {K : ℝ} (hbound : SmoothCompactVarianceGradientBound μ K) :
    BoundedVarianceGradientBound μ K := by
  intro f hf hgi B hB hfB
  have hf2 : MemLp f 2 μ := MemLp.of_bound
    hf.continuous.aestronglyMeasurable B (Eventually.of_forall hfB)
  let g (k : ℕ) (x : Space n) := smoothCutoff n k x * f x
  have hg (k : ℕ) : LocallyLipschitz (g k) :=
    (show ContDiff ℝ 1 (fun p : ℝ × ℝ => p.1 * p.2) from
      contDiff_fst.mul contDiff_snd).locallyLipschitz.comp
        ((smoothCutoff_contDiff k).locallyLipschitz.prodMk hf)
  have hgc (k : ℕ) : HasCompactSupport (g k) :=
    (smoothCutoff_hasCompactSupport k).mul_right
  have hvar := variance_tendsto_of_eLpNorm_sub_tendsto_zero
    (fun k => memLp_smoothCutoff_mul hf2 k) hf2
      (eLpNorm_smoothCutoff_mul_sub_tendsto_zero hf2)
  have hgrad := integral_norm_gradient_smoothCutoff_mul_tendsto hμ hf
    (hf2.integrable (by norm_num)) hgi
  apply le_of_tendsto_of_tendsto hvar (hgrad.const_mul (K * B))
  apply Eventually.of_forall
  intro k
  apply variance_le_gradient_L1_of_smooth_compact_variance_bound hμ hbound
    (hg k) (hgc k) hB
  intro x
  change |smoothCutoff n k x * f x| ≤ B
  rw [abs_mul, abs_of_nonneg (faithfulCutoff_bounds k x).1]
  exact (mul_le_mul_of_nonneg_right (faithfulCutoff_bounds k x).2 (abs_nonneg _)).trans
    (by simpa using hfB x)

/-- The complete criterion also passes to the actual weak law limit once the
limiting probability law is absolutely continuous. -/
theorem boundedVarianceGradientBound_of_weak_measure_limit
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : μ ≪ volume)
    {ν : ℕ → Measure (Space n)} [∀ k, IsProbabilityMeasure (ν k)] {K : ℝ}
    (hbound : ∀ᶠ k in atTop, SmoothCompactVarianceGradientBound (ν k) K)
    (hlim : ∀ f : Space n → ℝ, Continuous f → HasCompactSupport f →
      Tendsto (fun k => ∫ x, f x ∂ν k) atTop (𝓝 (∫ x, f x ∂μ))) :
    BoundedVarianceGradientBound μ K :=
  boundedVarianceGradientBound_of_smooth_compact hμ
    (smoothCompactVarianceGradientBound_of_weak_measure_limit hbound hlim)

end KLS
end

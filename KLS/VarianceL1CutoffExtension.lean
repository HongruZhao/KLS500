import KLS.VarianceL1MollifierExtension

open MeasureTheory Set Filter
open scoped Topology ContDiff ENNReal NNReal

noncomputable section
namespace KLS
variable {n : ℕ}

/-- Actual cutoffs extend the bounded variance estimate to every bounded locally
Lipschitz function with integrable actual gradient. -/
theorem variance_le_gradient_L1_of_poincare_bounded_locallyLipschitz
    {φ : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hconv : ConvexOn ℝ univ φ)
    {C : ℝ≥0} (hC : C ∈ poincareConstants (potentialMeasure φ)) (hC0 : 0 < (C : ℝ))
    {f : Space n → ℝ} (hf : LocallyLipschitz f)
    (hgi : Integrable (gradient f) (potentialMeasure φ))
    {B : ℝ} (hB : 0 ≤ B) (hfB : ∀ x, |f x| ≤ B) :
    ProbabilityTheory.variance f (potentialMeasure φ) ≤
      (16/3 : ℝ)*B*Real.sqrt C*(∫ x, ‖gradient f x‖ ∂potentialMeasure φ) := by
  have hμ : potentialMeasure φ ≪ volume := withDensity_absolutelyContinuous _ _
  have hf2 : MemLp f 2 (potentialMeasure φ) := MemLp.of_bound
    hf.continuous.aestronglyMeasurable B (Eventually.of_forall hfB)
  let g (k : ℕ) (x : Space n) := smoothCutoff n k x*f x
  have hg (k : ℕ) : LocallyLipschitz (g k) :=
    (show ContDiff ℝ 1 (fun p : ℝ × ℝ => p.1*p.2) from
      contDiff_fst.mul contDiff_snd).locallyLipschitz.comp
        ((smoothCutoff_contDiff k).locallyLipschitz.prodMk hf)
  have hgc (k : ℕ) : HasCompactSupport (g k) := (smoothCutoff_hasCompactSupport k).mul_right
  have hvar := variance_tendsto_of_eLpNorm_sub_tendsto_zero
    (fun k => memLp_smoothCutoff_mul hf2 k) hf2 (eLpNorm_smoothCutoff_mul_sub_tendsto_zero hf2)
  have hgrad := integral_norm_gradient_smoothCutoff_mul_tendsto hμ hf
    (hf2.integrable (by norm_num)) hgi
  apply le_of_tendsto_of_tendsto hvar (hgrad.const_mul ((16/3 : ℝ)*B*Real.sqrt C))
  apply Eventually.of_forall
  intro k
  apply variance_le_gradient_L1_of_poincare_compact_locallyLipschitz hφ hconv hC hC0
    (hg k) (hgc k) hB
  intro x
  change |smoothCutoff n k x*f x| ≤ B
  rw [abs_mul,abs_of_nonneg (faithfulCutoff_bounds k x).1]
  exact (mul_le_mul_of_nonneg_right (faithfulCutoff_bounds k x).2 (abs_nonneg _)).trans
    (by simpa using hfB x)

end KLS
end

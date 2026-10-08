import KLS.WeightedResolventVarianceL1Bound
import KLS.L1SmoothTestExtension
import KLS.PoincareGraphLimit

open MeasureTheory Set Filter
open scoped Topology ContDiff ENNReal NNReal

noncomputable section
namespace KLS
variable {n : ℕ}

/-- Actual L2 convergence gives continuity of the scalar variance. -/
theorem variance_tendsto_of_eLpNorm_sub_tendsto_zero
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    {f : ℕ → Space n → ℝ} {g : Space n → ℝ}
    (hf : ∀ k, MemLp (f k) 2 μ) (hg : MemLp g 2 μ)
    (hlim : Tendsto (fun k => eLpNorm (f k - g) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => ProbabilityTheory.variance (f k) μ) atTop
      (𝓝 (ProbabilityTheory.variance g μ)) := by
  have hLp := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf g hg).mpr hlim
  simpa only [Function.comp_def,norm_center_toLp_sq_eq_variance] using
    (((continuous_centeredL2_center μ).tendsto _).comp hLp).norm.pow 2

/-- Actual compact mollifiers preserve the uniform bound and converge in the
literal L1 gradient, extending the proved smooth estimate. -/
theorem variance_le_gradient_L1_of_poincare_compact_locallyLipschitz
    {φ : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hconv : ConvexOn ℝ univ φ)
    {C : ℝ≥0} (hC : C ∈ poincareConstants (potentialMeasure φ)) (hC0 : 0 < (C : ℝ))
    {f : Space n → ℝ} (hf : LocallyLipschitz f) (hfc : HasCompactSupport f)
    {B : ℝ} (hB : 0 ≤ B) (hfB : ∀ x, |f x| ≤ B) :
    ProbabilityTheory.variance f (potentialMeasure φ) ≤
      (16/3 : ℝ)*B*Real.sqrt C*(∫ x, ‖gradient f x‖ ∂potentialMeasure φ) := by
  have hμ : potentialMeasure φ ≪ volume := withDensity_absolutelyContinuous _ _
  have hs := compact_locallyLipschitz_absolutelyContinuous_smoothing hμ hf hfc
  have hf2 : MemLp f 2 (potentialMeasure φ) := MemLp.of_bound
    hf.continuous.aestronglyMeasurable B (Eventually.of_forall hfB)
  have hvar := variance_tendsto_of_eLpNorm_sub_tendsto_zero
    (fun k => (hs.1 k).2.2.1) hf2 hs.2.1
  have hgrad := integral_norm_gradient_mollify_tendsto hμ hf hfc
  apply le_of_tendsto_of_tendsto hvar (hgrad.const_mul ((16/3 : ℝ)*B*Real.sqrt C))
  apply Eventually.of_forall
  intro k
  apply variance_le_gradient_L1_of_poincare_smooth_compact hφ hconv hC hC0
    (mollify_contDiff hf.continuous.locallyIntegrable k) (hasCompactSupport_mollify hfc k) hB
  intro x
  exact norm_mollify_le_of_ae_bound (Eventually.of_forall hfB) k x

end KLS
end

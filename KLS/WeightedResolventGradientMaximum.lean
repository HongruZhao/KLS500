import KLS.WeightedResolventGradientCutoff
import KLS.WeightedResolventMaximumPrinciple

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology ContDiff ENNReal RealInnerProductSpace

noncomputable section
namespace KLS
variable {n : ℕ}

/-- The true elliptic resolvent equation contracts the gradient supremum on
its actual L2 diffusion/gradient domain under nonnegative curvature. Global
Hessian integrability is derived, and the monotone cutoff errors tend to zero. -/
theorem norm_gradient_le_of_resolvent_diffusion_domain {φ f g : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 1 g)
    {t : ℝ} (ht : 0 < t) (heq : ∀ x, f x-t*weightedDiffusion φ f x=g x)
    (hcurv : ∀ x, 0 ≤ hessianGradientForm φ f x)
    (hL : MemLp (weightedDiffusion φ f) 2 (potentialMeasure φ))
    (hG : Integrable (fun x => ‖gradient f x‖ ^ 2) (potentialMeasure φ))
    {M : ℝ} (hM : 0 ≤ M) (hgM : ∀ x, ‖gradient g x‖ ≤ M) :
    ∀ x, ‖gradient f x‖ ≤ M := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hH := (integrable_bochner_terms_of_diffusion_domain hφ hf hcurv hL hG).1
  have hF := gradientLevelDefect_integrable hf1 hg hgM hG
  have hF0 := gradientLevelDefect_nonneg hM hgM (f := f)
  obtain ⟨K,hK,hbound⟩ := smoothCutoff_gradient_bound (n := n)
  let c := fun k => cutoffScale k*K
  have hc0 (k : ℕ) : 0 ≤ c k := mul_nonneg (cutoffScale_pos k).le hK
  have hct : Tendsto c atTop (𝓝 0) := by
    simpa only [c,zero_mul] using cutoffScale_tendsto_zero.mul_const K
  have hB (k : ℕ) :
      (∫ x, smoothCutoff n k x ^ 2*gradientLevelDefect f g M x ∂potentialMeasure φ) ≤
        t*c k*(∫ x, hessianSquare f x+‖gradient f x‖ ^ 2 ∂potentialMeasure φ) := by
    apply integral_gradientLevelDefect_cutoff_le hφ hf hg
      ((smoothCutoff_contDiff k).of_le (by simp)) (smoothCutoff_hasCompactSupport k)
      (fun x => ?_) (hc0 k) (hbound k) ht heq hcurv hH hG M
    have hb := faithfulCutoff_bounds k x
    nlinarith
  have hlim := integral_smoothCutoff_sq_tendsto hF hF0
  have herr : Tendsto
      (fun k => t*c k*(∫ x, hessianSquare f x+‖gradient f x‖ ^ 2 ∂potentialMeasure φ))
      atTop (𝓝 0) := by
    simpa only [mul_zero,zero_mul] using (hct.const_mul t).mul_const
      (∫ x, hessianSquare f x+‖gradient f x‖ ^ 2 ∂potentialMeasure φ)
  have hz : (∫ x, gradientLevelDefect f g M x ∂potentialMeasure φ) = 0 :=
    le_antisymm (le_of_tendsto_of_tendsto hlim herr (Eventually.of_forall hB))
      (integral_nonneg hF0)
  have hae := (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall hF0) hF).mp hz
  apply continuous_le_const_of_ae_potentialMeasure hφ.continuous
    (continuous_gradient_of_contDiff hf1).norm
  filter_upwards [hae] with x hx
  by_contra hn
  have hp := gradientLevelDefect_pos_of_gradient_gt hM hgM (lt_of_not_ge hn)
  change gradientLevelDefect f g M x = 0 at hx
  linarith

end KLS
end

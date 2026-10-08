import KLS.BoundedWeightedMollification
import KLS.WeakDerivativeMollification

open MeasureTheory Set Filter ContinuousLinearMap
open scoped ContDiff Topology ENNReal Convolution
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- Bounded actual mollifications of a compact raw test converge against
 locally L1 coefficients. The common compact enlargement supplies the
 integrable dominating function; no approximating sequence is assumed. -/
theorem bounded_compact_mollify_localL1_pairing
    {f b : Space n → ℝ} (hf : LocallyIntegrable f volume)
    (hc : HasCompactSupport f) {C : ℝ}
    (hbound : ∀ᵐ x ∂volume, ‖f x‖ ≤ C) (hb : LocallyIntegrable b volume) :
    Integrable (fun x => b x*f x) ∧
      Tendsto (fun k => ∫ x, b x*mollify k f x) atTop (𝓝 (∫ x, b x*f x)) := by
  let S := mollifierEnlargement (tsupport f)
  have hS : IsCompact S := isCompact_mollifierEnlargement hc
  have hbS : Integrable (S.indicator b) volume :=
    (integrable_indicator_iff hS.measurableSet).mpr (hb.integrableOn_isCompact hS)
  have hdom : Integrable (fun x => C*‖S.indicator b x‖) volume := hbS.norm.const_mul C
  have hpoint {g : Space n → ℝ} (hgs : tsupport g ⊆ S)
      (hgb : ∀ᵐ x ∂volume, ‖g x‖ ≤ C) :
      ∀ᵐ x ∂volume, ‖b x*g x‖ ≤ C*‖S.indicator b x‖ := by
    filter_upwards [hgb] with x hx
    by_cases hxS : x ∈ S
    · rw [indicator_of_mem hxS,norm_mul]
      exact (mul_le_mul_of_nonneg_left hx (norm_nonneg _)).trans_eq (mul_comm _ _)
    · have hg0 : g x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hxS (hgs h))
      rw [hg0,mul_zero,norm_zero,indicator_of_notMem hxS,norm_zero,mul_zero]
  have hfS : tsupport f ⊆ S := by
    intro x hx
    have hz : (0 : Space n) ∈ Metric.closedBall 0 2 := by simp
    simpa only [S,mollifierEnlargement,add_zero] using Set.add_mem_add hx hz
  have hfm : AEStronglyMeasurable (fun x => b x*f x) volume :=
    hb.aestronglyMeasurable.mul hf.aestronglyMeasurable
  have hfi : Integrable (fun x => b x*f x) volume :=
    hdom.mono' hfm (hpoint hfS hbound)
  refine ⟨hfi,?_⟩
  exact tendsto_integral_of_dominated_convergence (fun x => C*‖S.indicator b x‖)
    (fun k => hb.aestronglyMeasurable.mul (mollify_contDiff hf k).continuous.aestronglyMeasurable)
    hdom (fun k => hpoint (tsupport_mollify_subset hc k)
      (Eventually.of_forall fun x => norm_mollify_le_of_ae_bound hbound k x))
    ((mollify_tendsto_ae hf).mono fun x hx => hx.const_mul (b x))


/-- The actual positive convolution kernels preserve almost everywhere
 nonnegativity at every point. -/
theorem mollify_nonneg_of_ae {f : Space n → ℝ}
    (hf : ∀ᵐ x ∂volume, 0 ≤ f x) (k : ℕ) (x : Space n) :
    0 ≤ mollify k f x := by
  unfold mollify scalarConvolution
  rw [convolution_def]
  apply integral_nonneg_of_ae
  filter_upwards [hf] with y hy
  change 0 ≤ f y*mollifierKernel n k (x-y)
  exact mul_nonneg hy ((mollifierBump n k).nonneg_normed _)

end KLS
end

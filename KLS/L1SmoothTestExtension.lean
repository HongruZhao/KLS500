import KLS.L1MollificationGradient

open MeasureTheory Set Filter
open scoped Topology ENNReal

noncomputable section
namespace KLS
variable {n : ℕ}

theorem lintegral_abs_mollify_sub_tendsto_zero
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : μ ≪ volume)
    {f : Space n → ℝ} (hf : LocallyLipschitz f) (hc : HasCompactSupport f) :
    Tendsto (fun k => ∫⁻ x, ENNReal.ofReal |mollify k f x - f x| ∂μ) atTop (𝓝 0) := by
  have hs := compact_locallyLipschitz_absolutelyContinuous_smoothing hμ hf hc
  exact lintegral_abs_tendsto_zero_of_eLpNorm_two
    (fun k => ((hs.1 k).1.continuous.aestronglyMeasurable.sub hf.continuous.aestronglyMeasurable)) hs.2.1

theorem integral_norm_gradient_mollify_tendsto
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : μ ≪ volume)
    {f : Space n → ℝ} (hf : LocallyLipschitz f) (hc : HasCompactSupport f) :
    Tendsto (fun k => ∫ x, ‖gradient (mollify k f) x‖ ∂μ)
      atTop (𝓝 (∫ x, ‖gradient f x‖ ∂μ)) := by
  have hs := compact_locallyLipschitz_absolutelyContinuous_smoothing hμ hf hc
  have hi (k : ℕ) : Integrable (gradient (mollify k f)) μ :=
    integrable_gradient_of_compact_locallyLipschitz ((hs.1 k).1.of_le (by norm_num) : ContDiff ℝ 1 (mollify k f)).locallyLipschitz (hs.1 k).2.1
  apply tendsto_integral_of_L1 (fun x => ‖gradient f x‖)
    (integrable_gradient_of_compact_locallyLipschitz hf hc).norm.aestronglyMeasurable
    (Eventually.of_forall fun k => (hi k).norm)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (lintegral_gradient_mollify_sub_tendsto_zero hμ hf hc)
    (fun _ => zero_le) (fun k => lintegral_mono fun x => ?_)
  rw [← ofReal_norm]
  apply ENNReal.ofReal_le_ofReal
  simpa only [Real.norm_eq_abs] using abs_norm_sub_norm_le (gradient (mollify k f) x) (gradient f x)

theorem lintegral_norm_gradient_mollify_tendsto
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : μ ≪ volume)
    {f : Space n → ℝ} (hf : LocallyLipschitz f) (hc : HasCompactSupport f) :
    Tendsto (fun k => ∫⁻ x, ENNReal.ofReal ‖gradient (mollify k f) x‖ ∂μ)
      atTop (𝓝 (∫⁻ x, ENNReal.ofReal ‖gradient f x‖ ∂μ)) := by
  have hs := compact_locallyLipschitz_absolutelyContinuous_smoothing hμ hf hc
  have ht := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (integral_norm_gradient_mollify_tendsto hμ hf hc)
  have he (k : ℕ) := ofReal_integral_eq_lintegral_ofReal
    (integrable_gradient_of_compact_locallyLipschitz ((hs.1 k).1.of_le (by norm_num) : ContDiff ℝ 1 (mollify k f)).locallyLipschitz (hs.1 k).2.1).norm
    (ae_of_all μ fun x => norm_nonneg (gradient (mollify k f) x))
  have he0 := ofReal_integral_eq_lintegral_ofReal
    (integrable_gradient_of_compact_locallyLipschitz hf hc).norm
    (ae_of_all μ fun x => norm_nonneg (gradient f x))
  simpa only [Function.comp_def, he, he0] using ht

/-- A genuine smooth compact-test L1 estimate suffices for the full locally
 Lipschitz median inequality under any absolutely continuous probability law.
 Actual mollifiers and actual spatial cutoffs supply both limiting steps.
 This proves the domain extension, not the compact-test analytic estimate. -/
theorem l1MedianCheeger_of_smooth_compact_tests
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : μ ≪ volume)
    {C : ℝ} (hC : 0 < C)
    (htest : ∀ g : Space n → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
      ∃ a : ℝ, (∫⁻ x, ENNReal.ofReal |g x - a| ∂μ) ≤
        ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal ‖gradient g x‖ ∂μ) :
    L1MedianCheeger μ C := by
  apply l1MedianCheeger_of_compact_locallyLipschitz_tests hμ hC
  intro f hf hc hfi _
  have hg (k : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (mollify k f) :=
    mollify_contDiff hf.continuous.locallyIntegrable k
  have hb := fun k => htest (mollify k f) (hg k) (hasCompactSupport_mollify hc k)
  choose a ha using hb
  have herror : Tendsto (fun k => ∫⁻ x, ENNReal.ofReal |f x - mollify k f x| ∂μ)
      atTop (𝓝 0) := by
    simpa only [abs_sub_comm] using lintegral_abs_mollify_sub_tendsto_zero hμ hf hc
  have hB := ENNReal.Tendsto.const_mul
    (lintegral_norm_gradient_mollify_tendsto hμ hf hc) (Or.inr (ENNReal.ofReal_ne_top (r := C)))
  obtain ⟨m, _, hm⟩ := exists_probabilityMedian_lintegral_le_of_approximation
    hf.continuous.measurable hfi (fun k => (hg k).continuous.measurable) a ha herror hB
  exact ⟨m, hm⟩

end KLS
end

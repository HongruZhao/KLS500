import KLS.L1CutoffDomain
import KLS.MedianL1Approximation

open MeasureTheory Set Filter
open scoped Topology ENNReal

noncomputable section
namespace KLS
variable {n : ℕ}

/-- The actual extended gradient integrals of spatial cutoffs converge whenever
 the original actual gradient is integrable. -/
theorem lintegral_norm_gradient_smoothCutoff_mul_tendsto
    {μ : Measure (Space n)} (hμ : μ ≪ volume) {f : Space n → ℝ}
    (hf : LocallyLipschitz f) (hfi : Integrable f μ) (hgi : Integrable (gradient f) μ) :
    Tendsto (fun k => ∫⁻ x, ENNReal.ofReal
      ‖gradient (fun y => smoothCutoff n k y * f y) x‖ ∂μ)
      atTop (𝓝 (∫⁻ x, ENNReal.ofReal ‖gradient f x‖ ∂μ)) := by
  have ht := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (integral_norm_gradient_smoothCutoff_mul_tendsto hμ hf hfi hgi)
  have he (k : ℕ) := ofReal_integral_eq_lintegral_ofReal
    (integrable_gradient_smoothCutoff_mul hμ hf hfi hgi k).norm
    (ae_of_all μ fun x => norm_nonneg (gradient (fun y => smoothCutoff n k y * f y) x))
  have he0 := ofReal_integral_eq_lintegral_ofReal hgi.norm
    (ae_of_all μ fun x => norm_nonneg (gradient f x))
  simpa only [Function.comp_def, he, he0] using ht

/-- A compact locally Lipschitz test inequality extends to the full L1 median
 domain. The genuine compact-test analytic estimate is an explicit premise;
 the cutoff, gradient convergence and limit median are constructed here. -/
theorem l1MedianCheeger_of_compact_locallyLipschitz_tests
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : μ ≪ volume)
    {C : ℝ} (hC : 0 < C)
    (hcompact : ∀ g : Space n → ℝ, LocallyLipschitz g → HasCompactSupport g →
      Integrable g μ → Integrable (gradient g) μ →
      ∃ a : ℝ, (∫⁻ x, ENNReal.ofReal |g x - a| ∂μ) ≤
        ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal ‖gradient g x‖ ∂μ) :
    L1MedianCheeger μ C := by
  intro f hf hfi
  by_cases hgt : (∫⁻ x, ENNReal.ofReal ‖gradient f x‖ ∂μ) = ⊤
  · obtain ⟨m, hm⟩ := exists_probabilityMedian μ hf.continuous.measurable
    refine ⟨m, hm, ?_⟩
    rw [hgt, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hC).ne']
    exact le_top
  have hgi : Integrable (gradient f) μ :=
    ⟨(measurable_gradient f).aestronglyMeasurable,
      (hasFiniteIntegral_iff_norm _).mpr (lt_top_iff_ne_top.mpr hgt)⟩
  let g (k : ℕ) (x : Space n) := smoothCutoff n k x * f x
  have hg (k : ℕ) : LocallyLipschitz (g k) :=
    (show ContDiff ℝ 1 (fun p : ℝ × ℝ => p.1 * p.2) from
      contDiff_fst.mul contDiff_snd).locallyLipschitz.comp
        ((smoothCutoff_contDiff k).locallyLipschitz.prodMk hf)
  have hgc (k : ℕ) : HasCompactSupport (g k) := (smoothCutoff_hasCompactSupport k).mul_right
  have hbound := fun k => hcompact (g k) (hg k) (hgc k)
    (integrable_smoothCutoff_mul hfi k) (integrable_gradient_smoothCutoff_mul hμ hf hfi hgi k)
  choose a ha using hbound
  apply exists_probabilityMedian_lintegral_le_of_approximation hf.continuous.measurable hfi
    (fun k => (hg k).continuous.measurable) a ha
  · simpa only [abs_sub_comm] using lintegral_abs_smoothCutoff_mul_sub_tendsto_zero hfi
  · exact ENNReal.Tendsto.const_mul
      (lintegral_norm_gradient_smoothCutoff_mul_tendsto hμ hf hfi hgi)
      (Or.inr (ENNReal.ofReal_ne_top))

end KLS
end

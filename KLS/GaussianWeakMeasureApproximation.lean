import KLS.PoincareWeakMeasureLimit
import KLS.IsotropicGaussianSmoothing

/-! The actual normalized Gaussian laws converge on every compact continuous test. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
noncomputable section
namespace KLS
variable {n : ℕ}

theorem tendsto_integral_isotropicGaussianSmoothing_compact
    (μ : Measure (Space n)) [IsProbabilityMeasure μ] {f : Space n → ℝ}
    (hf : Continuous f) (hc : HasCompactSupport f) :
    Tendsto (fun k => ∫ x, f x ∂isotropicGaussianSmoothing μ (cutoffScale k))
      atTop (𝓝 (∫ x, f x ∂μ)) := by
  obtain ⟨B, hB⟩ := (hc.isCompact_range hf).isBounded.exists_norm_le
  have hb (x : Space n) : ‖f x‖ ≤ B := hB (f x) (mem_range_self x)
  have ht := tendsto_integral_of_dominated_convergence (fun _ : Space n × Space n => B)
    (fun k => (hf.comp (by fun_prop : Continuous (fun p : Space n × Space n =>
      gaussianNormalization (cutoffScale k) • (p.1 + cutoffScale k • p.2)))).aestronglyMeasurable)
    (μ := μ.prod (gaussianExample n)) (integrable_const _)
    (fun _ => Eventually.of_forall fun _ => hb _)
    (Eventually.of_forall fun p => by
      have hg := gaussianNormalization_tendsto.comp cutoffScale_tendsto_zero
      have hx := (tendsto_const_nhds (x := p.1)).add
        (cutoffScale_tendsto_zero.smul_const p.2)
      simpa only [zero_smul, add_zero, one_smul, Function.comp_def] using
        (hf.continuousAt.tendsto.comp (hg.smul hx)))
  have he (k : ℕ) : (∫ x, f x ∂isotropicGaussianSmoothing μ (cutoffScale k)) =
      ∫ p : Space n × Space n,
        f (gaussianNormalization (cutoffScale k) • (p.1 + cutoffScale k • p.2))
          ∂μ.prod (gaussianExample n) := by
    rw [isotropicGaussianSmoothing, integral_map (by fun_prop) hf.aestronglyMeasurable]
    exact integral_gaussianSmoothing_eq_prod μ _ (by fun_prop)
  simp_rw [he]
  simpa only [integral_fun_fst (μ := μ) (ν := gaussianExample n), probReal_univ,
    one_smul, Function.comp_def] using ht

theorem mem_poincareConstants_of_isotropicGaussianSmoothing
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : μ ≪ volume)
    {C : ℝ≥0} (hC : 0 < C)
    (hbound : ∀ᶠ k in atTop, C ∈ poincareConstants
      (isotropicGaussianSmoothing μ (cutoffScale k))) : C ∈ poincareConstants μ :=
  mem_poincareConstants_of_weak_measure_limit hμ hC hbound
    (fun _ hf hc => tendsto_integral_isotropicGaussianSmoothing_compact μ hf hc)

end KLS
end

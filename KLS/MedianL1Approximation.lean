import KLS.MedianL1Minimizer

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

noncomputable section
namespace KLS

/-- L¹ convergence transfers centered deviation bounds to a genuine median of
the limit. The approximants' centers need not be medians or converge. -/
theorem exists_probabilityMedian_lintegral_le_of_approximation
    {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    {f : Space n → ℝ} (hf : Measurable f) (hfi : Integrable f μ)
    {g : ℕ → Space n → ℝ} (hg : ∀ j, Measurable (g j))
    (a : ℕ → ℝ) {B : ℕ → ℝ≥0∞} {b : ℝ≥0∞}
    (hbound : ∀ j, (∫⁻ x, ENNReal.ofReal |g j x - a j| ∂μ) ≤ B j)
    (herror : Tendsto (fun j => ∫⁻ x, ENNReal.ofReal |f x - g j x| ∂μ) atTop (𝓝 0))
    (hB : Tendsto B atTop (𝓝 b)) :
    ∃ m : ℝ, IsProbabilityMedian μ f m ∧
      (∫⁻ x, ENNReal.ofReal |f x - m| ∂μ) ≤ b := by
  obtain ⟨m, hm⟩ := exists_probabilityMedian μ hf
  refine ⟨m, hm, ?_⟩
  have hle : ∀ j, (∫⁻ x, ENNReal.ofReal |f x - m| ∂μ) ≤
      (∫⁻ x, ENNReal.ofReal |f x - g j x| ∂μ) + B j := by
    intro j
    exact (hm.lintegral_abs_sub_le_approx hf hfi (hg j) (a j)).trans
      (add_le_add le_rfl (hbound j))
  have hlim : Tendsto (fun j => (∫⁻ x, ENNReal.ofReal |f x - g j x| ∂μ) + B j)
      atTop (𝓝 b) := by simpa only [zero_add] using herror.add hB
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim (Eventually.of_forall hle)

end KLS
end

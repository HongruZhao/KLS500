import KLS.WeakDerivativeMollification

open MeasureTheory Filter
open scoped Topology
noncomputable section
namespace KLS

/-- Pairing an actual L1 sequence with an almost everywhere bounded
 measurable observable preserves integrability and its vanishing L1 limit. -/
theorem bounded_pairing_tendsto_zero_of_integral_norm
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : ℕ → α → ℝ} {b : α → ℝ} {C : ℝ}
    (hb : AEStronglyMeasurable b μ) (hbound : ∀ᵐ x ∂μ, ‖b x‖ ≤ C)
    (hf : ∀ k, Integrable (f k) μ)
    (hlim : Tendsto (fun k => ∫ x, ‖f k x‖ ∂μ) atTop (𝓝 0)) :
    (∀ k, Integrable (fun x => b x*f k x) μ) ∧
      Tendsto (fun k => ∫ x, b x*f k x ∂μ) atTop (𝓝 0) := by
  refine ⟨fun k => (hf k).bdd_mul hb hbound,?_⟩
  have hnorm (k : ℕ) : ‖∫ x, b x*f k x ∂μ‖ ≤ C*(∫ x, ‖f k x‖ ∂μ) := by
    rw [← integral_const_mul]
    apply norm_integral_le_of_norm_le ((hf k).norm.const_mul C)
    filter_upwards [hbound] with x hx
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
  exact squeeze_zero_norm hnorm (by simpa only [mul_zero] using hlim.const_mul C)

end KLS
end

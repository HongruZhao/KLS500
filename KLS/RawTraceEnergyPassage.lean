import KLS.HessianMetricIntegrationExtension

open MeasureTheory Filter
open scoped Topology

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Actual integrable cutoffs bounded by one pass to an integrable function
without any continuity assumption on that function. -/
theorem integral_mul_tendsto_of_ae_bounded_cutoffs
    {f : α → ℝ} {χ : ℕ → α → ℝ} (hf : Integrable f μ)
    (hχm : ∀ k, AEStronglyMeasurable (χ k) μ)
    (hχ : ∀ k, ∀ᵐ x ∂μ, ‖χ k x‖ ≤ 1)
    (hχlim : ∀ᵐ x ∂μ, Tendsto (fun k => χ k x) atTop (𝓝 1)) :
    (∀ k, Integrable (fun x => χ k x * f x) μ) ∧
      Tendsto (fun k => ∫ x, χ k x * f x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
  have hi (k : ℕ) : Integrable (fun x => χ k x * f x) μ :=
    hf.bdd_mul (hχm k) (hχ k)
  refine ⟨hi, ?_⟩
  apply tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
    (fun k => (hi k).aestronglyMeasurable) hf.norm
  · intro k
    filter_upwards [hχ k] with x hx
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hx
  · filter_upwards [hχlim] with x hx
    simpa only [one_mul] using hx.mul_const (f x)

/-- Positive Fatou first derives global integrability from literal localized
balance identities. The cutoff balance and its vanishing error are explicit
inputs; this theorem does not establish a weak Monge-Ampere equation. -/
theorem integrable_nonneg_of_cutoff_balance
    {S G : α → ℝ} {χ : ℕ → α → ℝ} {error : ℕ → ℝ}
    (hS : Integrable S μ) (hGm : AEStronglyMeasurable G μ)
    (hGn : ∀ᵐ x ∂μ, 0 ≤ G x)
    (hχm : ∀ k, AEStronglyMeasurable (χ k) μ)
    (hχ : ∀ k, ∀ᵐ x ∂μ, 0 ≤ χ k x ∧ χ k x ≤ 1)
    (hχlim : ∀ᵐ x ∂μ, Tendsto (fun k => χ k x) atTop (𝓝 1))
    (hχGi : ∀ k, Integrable (fun x => χ k x * G x) μ)
    (herror : Tendsto error atTop (𝓝 0))
    (hbalance : ∀ k, (∫ x, χ k x * G x ∂μ) =
      (∫ x, χ k x * S x ∂μ) + error k) :
    Integrable G μ ∧ (∫ x, G x ∂μ) = ∫ x, S x ∂μ := by
  have hχnorm (k : ℕ) : ∀ᵐ x ∂μ, ‖χ k x‖ ≤ 1 := by
    filter_upwards [hχ k] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
    exact hx.2
  have hSlim := (integral_mul_tendsto_of_ae_bounded_cutoffs hS hχm hχnorm hχlim).2
  have hGlim : Tendsto (fun k => ∫ x, χ k x * G x ∂μ)
      atTop (𝓝 (∫ x, S x ∂μ)) := by
    simp_rw [hbalance]
    simpa only [add_zero] using hSlim.add herror
  have hnorm (k : ℕ) : (∫ x, ‖χ k x * G x‖ ∂μ) = ∫ x, χ k x * G x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hχ k, hGn] with x hx hg
    exact Real.norm_of_nonneg (mul_nonneg hx.1 hg)
  have hGi : Integrable G μ := by
    apply integrable_of_tendsto_integral_norm hGm hχGi
    · filter_upwards [hχlim] with x hx
      simpa only [one_mul] using hx.mul_const (G x)
    · simpa only [hnorm] using hGlim
  have hlim := (integral_mul_tendsto_of_ae_bounded_cutoffs hGi hχm hχnorm hχlim).2
  exact ⟨hGi, tendsto_nhds_unique hlim hGlim⟩

/-- The trace-energy integrability and half-trace estimate follow from an
actual localized balance, positivity, the tensor comparison and a vanishing
cutoff error. None of the three global energies is assumed integrable. -/
theorem trace_energy_integrability_and_half_of_cutoff_balance
    {S A F D : α → ℝ} {χ : ℕ → α → ℝ} {error : ℕ → ℝ}
    (hS : Integrable S μ)
    (hAm : AEStronglyMeasurable A μ) (hFm : AEStronglyMeasurable F μ)
    (hDm : AEStronglyMeasurable D μ)
    (hAn : ∀ᵐ x ∂μ, 0 ≤ A x) (hFn : ∀ᵐ x ∂μ, 0 ≤ F x)
    (hDn : ∀ᵐ x ∂μ, 0 ≤ D x) (hAD : ∀ᵐ x ∂μ, A x ≤ D x)
    (hχm : ∀ k, AEStronglyMeasurable (χ k) μ)
    (hχ : ∀ k, ∀ᵐ x ∂μ, 0 ≤ χ k x ∧ χ k x ≤ 1)
    (hχlim : ∀ᵐ x ∂μ, Tendsto (fun k => χ k x) atTop (𝓝 1))
    (hχGi : ∀ k, Integrable (fun x => χ k x * (A x + F x + D x)) μ)
    (herror : Tendsto error atTop (𝓝 0))
    (hbalance : ∀ k, (∫ x, χ k x * (A x + F x + D x) ∂μ) =
      (∫ x, χ k x * S x ∂μ) + error k) :
    Integrable A μ ∧ Integrable F μ ∧ Integrable D μ ∧
      (∫ x, S x ∂μ) = (∫ x, A x ∂μ) + (∫ x, F x ∂μ) + (∫ x, D x ∂μ) ∧
      (∫ x, A x ∂μ) ≤ (1 / 2 : ℝ) * ∫ x, S x ∂μ := by
  let G := fun x => A x + F x + D x
  have hGn : ∀ᵐ x ∂μ, 0 ≤ G x := by
    filter_upwards [hAn, hFn, hDn] with x ha hf hd
    exact add_nonneg (add_nonneg ha hf) hd
  obtain ⟨hGi, hGint⟩ := integrable_nonneg_of_cutoff_balance hS
    ((hAm.add hFm).add hDm) hGn hχm hχ hχlim hχGi herror hbalance
  have hAi : Integrable A μ := by
    apply hGi.mono' hAm
    filter_upwards [hAn, hFn, hDn] with x ha hf hd
    rw [Real.norm_of_nonneg ha]
    change A x ≤ A x + F x + D x
    linarith
  have hFi : Integrable F μ := by
    apply hGi.mono' hFm
    filter_upwards [hAn, hFn, hDn] with x ha hf hd
    rw [Real.norm_of_nonneg hf]
    change F x ≤ A x + F x + D x
    linarith
  have hDi : Integrable D μ := by
    apply hGi.mono' hDm
    filter_upwards [hAn, hFn, hDn] with x ha hf hd
    rw [Real.norm_of_nonneg hd]
    change D x ≤ A x + F x + D x
    linarith
  have hid : (∫ x, S x ∂μ) =
      (∫ x, A x ∂μ) + (∫ x, F x ∂μ) + (∫ x, D x ∂μ) := by
    calc
      (∫ x, S x ∂μ) = ∫ x, (A + F + D) x ∂μ := hGint.symm
      _ = (∫ x, (A + F) x ∂μ) + (∫ x, D x ∂μ) := integral_add (hAi.add hFi) hDi
      _ = _ := congrArg (fun t : ℝ => t + ∫ x, D x ∂μ) (integral_add hAi hFi)
  refine ⟨hAi, hFi, hDi, hid, ?_⟩
  have hle := integral_mono_ae hAi hDi hAD
  have hnonneg := integral_nonneg_of_ae hFn
  linarith

end KLS
end

import KLS.FaithfulPoincareSmoothCore
import KLS.WeightedOptimalPoincare

/-! Full faithful Poincare bounds pass to actual weak limits of probability laws. -/
open MeasureTheory Set Filter
open scoped Topology ContDiff NNReal ENNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

theorem real_smooth_poincare_bound_of_mem_constants
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] {C : ℝ≥0}
    (hC : C ∈ poincareConstants μ) {f : Space n → ℝ}
    (hf : ContDiff ℝ 3 f) (hc : HasCompactSupport f) :
    ProbabilityTheory.variance f μ ≤ (C : ℝ) *
      ∑ i : Fin n, ∫ x, coordinateDerivative f i x ^ 2 ∂μ := by
  have hf2 : MemLp f 2 μ := hf.continuous.memLp_of_hasCompactSupport hc
  have hd (i : Fin n) : MemLp (coordinateDerivative f i) 2 μ :=
    (contDiff_coordinateDerivative hf (m := 0) (by norm_num) i).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_coordinateDerivative hc i)
  have he := energy_lt_top_of_memLp_coordinateDerivative hd
  have hb := hC f ⟨(hf.of_le (by norm_num : (1 : ℕ∞ω) ≤ 3)).locallyLipschitz, hf2⟩
  have ht : (C : ℝ≥0∞) * energy μ f ≠ ⊤ :=
    (ENNReal.mul_lt_top ENNReal.coe_lt_top he).ne
  have hr := ENNReal.toReal_mono ht hb
  change ProbabilityTheory.variance f μ ≤ _ at hr
  rw [energy_eq_ofReal_sum_coordinate_integrals he, ENNReal.toReal_mul, ENNReal.coe_toReal,
    ENNReal.toReal_ofReal (Finset.sum_nonneg fun i _ => integral_nonneg fun x => sq_nonneg _)] at hr
  exact hr

/-- Convergence of integrals of actual continuous compact tests is sufficient:
the same positive constant passes to every original locally Lipschitz L2 test. -/
theorem mem_poincareConstants_of_weak_measure_limit
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : μ ≪ volume)
    {ν : ℕ → Measure (Space n)} [∀ k, IsProbabilityMeasure (ν k)]
    {C : ℝ≥0} (hC : 0 < C)
    (hbound : ∀ᶠ k in atTop, C ∈ poincareConstants (ν k))
    (hlim : ∀ f : Space n → ℝ, Continuous f → HasCompactSupport f →
      Tendsto (fun k => ∫ x, f x ∂ν k) atTop (𝓝 (∫ x, f x ∂μ))) :
    C ∈ poincareConstants μ := by
  apply mem_poincareConstants_of_compact_smooth_tests hμ hC
  intro f hf hc
  have hf2 (ρ : Measure (Space n)) [IsProbabilityMeasure ρ] : MemLp f 2 ρ :=
    hf.continuous.memLp_of_hasCompactSupport hc
  have hvar : Tendsto (fun k => ProbabilityTheory.variance f (ν k)) atTop
      (𝓝 (ProbabilityTheory.variance f μ)) := by
    have ht := (hlim (fun x => f x ^ 2) (hf.continuous.pow 2)
      (by simpa only [pow_two, Pi.mul_def] using hc.mul_right)).sub ((hlim f hf.continuous hc).pow 2)
    simpa only [ProbabilityTheory.variance_eq_sub (hf2 _), Pi.pow_apply] using ht
  have henergy : Tendsto
      (fun k => ∑ i : Fin n, ∫ x, coordinateDerivative f i x ^ 2 ∂ν k) atTop
      (𝓝 (∑ i : Fin n, ∫ x, coordinateDerivative f i x ^ 2 ∂μ)) := by
    apply tendsto_finsetSum Finset.univ
    intro i _
    apply hlim
    · exact (contDiff_coordinateDerivative hf (m := 0) (by norm_num) i).continuous.pow 2
    · simpa only [pow_two, Pi.mul_def] using (hasCompactSupport_coordinateDerivative hc i).mul_right
  apply le_of_tendsto_of_tendsto hvar (henergy.const_mul (C : ℝ))
  filter_upwards [hbound] with k hk
  exact real_smooth_poincare_bound_of_mem_constants hk hf hc

end KLS
end

import KLS.L1CheegerRamps
import Mathlib.Probability.CDF

open MeasureTheory Set Filter ProbabilityTheory Function
open scoped Topology ENNReal NNReal

noncomputable section
namespace KLS

/-- Every quantile level strictly between zero and one is crossed by a probability CDF,
including distributions with atoms. The left limit retains the lower-side inequality. -/
theorem exists_cdf_quantile (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    ∃ m : ℝ, q ≤ cdf μ m ∧ leftLim (cdf μ) m ≤ q := by
  let S : Set ℝ := {x | q ≤ cdf μ x}
  obtain ⟨b, hb⟩ := ((tendsto_cdf_atTop μ).eventually_const_lt hq1).exists
  have hS : S.Nonempty := ⟨b, hb.le⟩
  obtain ⟨a, ha⟩ := ((tendsto_cdf_atBot μ).eventually_lt_const hq0).exists
  have hSb : BddBelow S := by
    refine ⟨a, ?_⟩
    intro x hx
    by_contra hax
    have hfx := (monotone_cdf μ) (le_of_not_ge hax)
    exact (not_lt_of_ge hx) (hfx.trans_lt ha)
  let m := sInf S
  have hright : ∀ y : ℝ, m < y → q ≤ cdf μ y := by
    intro y hy
    obtain ⟨z, hzS, hzy⟩ := exists_lt_of_csInf_lt hS hy
    exact hzS.trans ((monotone_cdf μ) hzy.le)
  refine ⟨m, ?_, ?_⟩
  · rw [← (cdf μ).iInf_Ioi_eq m]
    exact le_ciInf fun y => hright y y.property
  · rw [(monotone_cdf μ).leftLim_eq_sSup]
    apply csSup_le
    · exact ⟨cdf μ (m - 1), m - 1, by simp, rfl⟩
    · rintro _ ⟨y, hy, rfl⟩
      by_contra hqy
      exact (not_le_of_gt hy) (csInf_le hSb (le_of_not_ge hqy))

/-- Every real probability measure admits a median, with both closed half-rays.
No atomlessness or moment assumption is used. -/
theorem exists_real_probability_median (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ∃ m : ℝ, (1 / 2 : ℝ≥0∞) ≤ μ (Iic m) ∧
      (1 / 2 : ℝ≥0∞) ≤ μ (Ici m) := by
  obtain ⟨m, hm, hl⟩ := exists_cdf_quantile μ (q := 1 / 2) (by norm_num) (by norm_num)
  refine ⟨m, ?_, ?_⟩
  · rw [← ofReal_cdf μ m]
    convert ENNReal.ofReal_le_ofReal hm using 1
    norm_num [ENNReal.ofReal_div_of_pos]
  · rw [← measure_cdf μ, (cdf μ).measure_Ici (tendsto_cdf_atTop μ)]
    have h : (1 / 2 : ℝ) ≤ 1 - leftLim (cdf μ) m := by linarith
    convert ENNReal.ofReal_le_ofReal h using 1
    norm_num [ENNReal.ofReal_div_of_pos]

/-- Median existence on the exact test domain used by `L1MedianCheeger`.
Measurability alone suffices; local Lipschitz continuity and integrability are not required. -/
theorem exists_probabilityMedian {n : ℕ} (μ : Measure (Space n)) [IsProbabilityMeasure μ]
    {f : Space n → ℝ} (hf : Measurable f) :
    ∃ m : ℝ, IsProbabilityMedian μ f m := by
  obtain ⟨m, hm, hm'⟩ := exists_real_probability_median (μ.map f)
  refine ⟨m, ?_, ?_⟩
  · rw [Measure.map_apply hf measurableSet_Iic] at hm
    exact hm
  · rw [Measure.map_apply hf measurableSet_Ici] at hm'
    exact hm'

end KLS

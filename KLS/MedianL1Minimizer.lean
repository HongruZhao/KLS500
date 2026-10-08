import KLS.ProbabilityMedians

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

noncomputable section
namespace KLS

/-- One half of the median property controls movement of the center to the right. -/
theorem integral_abs_sub_le_of_half_sublevel {n : ℕ} (μ : Measure (Space n))
    [IsProbabilityMeasure μ] {f : Space n → ℝ} (hf : Measurable f) (hfi : Integrable f μ)
    {m a : ℝ} (hma : m ≤ a) (hm : (1 / 2 : ℝ≥0∞) ≤ μ {x | f x ≤ m}) :
    (∫ x, |f x - m| ∂μ) ≤ ∫ x, |f x - a| ∂μ := by
  let S : Set (Space n) := {x | f x ≤ m}
  have hS : MeasurableSet S := measurableSet_le hf measurable_const
  have hSi : Integrable (S.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const 1).indicator hS
  have hmi : Integrable (fun x => |f x - m|) μ := (hfi.sub (integrable_const m)).abs
  have hai : Integrable (fun x => |f x - a|) μ := (hfi.sub (integrable_const a)).abs
  have hgi : Integrable (fun x => (2 * S.indicator (fun _ => (1 : ℝ)) x - 1) * (a - m)) μ :=
    ((hSi.const_mul 2).sub (integrable_const 1)).mul_const _
  have hpoint : ∀ x, |f x - m| +
      (2 * S.indicator (fun _ => (1 : ℝ)) x - 1) * (a - m) ≤ |f x - a| := by
    intro x
    by_cases hx : x ∈ S
    · have hxm : f x ≤ m := hx
      simp only [indicator_of_mem hx, abs_of_nonpos (sub_nonpos.mpr hxm),
        abs_of_nonpos (sub_nonpos.mpr (hxm.trans hma))]
      linarith
    · simp only [indicator_of_notMem hx]
      have ht := abs_add_le (f x - a) (a - m)
      rw [sub_add_sub_cancel, abs_of_nonneg (sub_nonneg.mpr hma)] at ht
      linarith
  have hint := integral_mono (hmi.add hgi) hai hpoint
  change (∫ x, |f x - m| + (2 * S.indicator (fun _ => (1 : ℝ)) x - 1) * (a - m) ∂μ) ≤ _ at hint
  rw [integral_add hmi hgi, integral_mul_const,
    integral_sub (hSi.const_mul 2) (integrable_const 1), integral_const_mul,
    integral_indicator_const 1 hS, integral_const] at hint
  have hmreal : (1 / 2 : ℝ) ≤ μ.real S := by
    have h := (ENNReal.toReal_le_toReal (by norm_num) (measure_ne_top μ S)).mpr hm
    simpa [measureReal_def] using h
  simp only [probReal_univ, smul_eq_mul, mul_one] at hint
  nlinarith [mul_nonneg (show 0 ≤ 2 * μ.real S - 1 by linarith) (sub_nonneg.mpr hma)]

/-- A probability median minimizes integrable absolute deviation over all real centers.
Both half-mass inequalities are needed; atomless laws are not assumed. -/
theorem IsProbabilityMedian.integral_abs_sub_le {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] {f : Space n → ℝ} {m : ℝ}
    (hm : IsProbabilityMedian μ f m) (hf : Measurable f) (hfi : Integrable f μ) (a : ℝ) :
    (∫ x, |f x - m| ∂μ) ≤ ∫ x, |f x - a| ∂μ := by
  rcases le_total m a with hma | ham
  · exact integral_abs_sub_le_of_half_sublevel μ hf hfi hma hm.1
  · have hneg : (1 / 2 : ℝ≥0∞) ≤ μ {x | -f x ≤ -m} := by
      simpa only [neg_le_neg_iff] using hm.2
    have h := integral_abs_sub_le_of_half_sublevel μ hf.neg hfi.neg (neg_le_neg ham) hneg
    simpa only [Pi.neg_apply, neg_sub_neg, abs_sub_comm] using h

/-- The same minimization statement in the extended-integral convention used by Cheeger. -/
theorem IsProbabilityMedian.lintegral_abs_sub_le {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] {f : Space n → ℝ} {m : ℝ}
    (hm : IsProbabilityMedian μ f m) (hf : Measurable f) (hfi : Integrable f μ) (a : ℝ) :
    (∫⁻ x, ENNReal.ofReal |f x - m| ∂μ) ≤ ∫⁻ x, ENNReal.ofReal |f x - a| ∂μ := by
  have hmi : Integrable (fun x => |f x - m|) μ := (hfi.sub (integrable_const m)).abs
  have hai : Integrable (fun x => |f x - a|) μ := (hfi.sub (integrable_const a)).abs
  rw [← ofReal_integral_eq_lintegral_ofReal hmi (ae_of_all μ fun _ => abs_nonneg _),
    ← ofReal_integral_eq_lintegral_ofReal hai (ae_of_all μ fun _ => abs_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (hm.integral_abs_sub_le hf hfi a)

/-- Approximation may use any centers, without convergence of those centers.
This is useful when extending a smooth L¹ estimate to the full locally Lipschitz domain. -/
theorem IsProbabilityMedian.lintegral_abs_sub_le_approx {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] {f g : Space n → ℝ} {m : ℝ}
    (hm : IsProbabilityMedian μ f m) (hf : Measurable f) (hfi : Integrable f μ)
    (hg : Measurable g) (a : ℝ) :
    (∫⁻ x, ENNReal.ofReal |f x - m| ∂μ) ≤
      (∫⁻ x, ENNReal.ofReal |f x - g x| ∂μ) +
      ∫⁻ x, ENNReal.ofReal |g x - a| ∂μ := by
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal |f x - a| ∂μ := hm.lintegral_abs_sub_le hf hfi a
    _ ≤ ∫⁻ x, ENNReal.ofReal |f x - g x| + ENNReal.ofReal |g x - a| ∂μ := by
      apply lintegral_mono
      intro x
      dsimp only
      rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (by simpa using abs_add_le (f x - g x) (g x - a))
    _ = _ := lintegral_add_left (by fun_prop) _

end KLS

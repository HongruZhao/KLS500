import KLS.QuadraticDamping

/-! Genuine nonnegative quadratic damping on an arbitrary probability law. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
noncomputable section
namespace KLS
variable {n : ℕ}

lemma exp_quadraticDamping_le_one {ε : ℝ} (hε : 0 ≤ ε) (x : Space n) :
    Real.exp (-ε * ‖x‖ ^ 2) ≤ 1 :=
  Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hε) (sq_nonneg _))

lemma integrable_exp_quadraticDamping (μ : Measure (Space n)) [IsFiniteMeasure μ]
    {ε : ℝ} (hε : 0 ≤ ε) : Integrable (fun x => Real.exp (-ε * ‖x‖ ^ 2)) μ :=
  (integrable_const (1 : ℝ)).mono' (by fun_prop)
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      using exp_quadraticDamping_le_one hε x)

lemma isProbabilityMeasure_quadraticDamping_nonneg (μ : Measure (Space n))
    [IsProbabilityMeasure μ] {ε : ℝ} (hε : 0 ≤ ε) :
    IsProbabilityMeasure (quadraticDamping μ ε) :=
  isProbabilityMeasure_tilted (integrable_exp_quadraticDamping μ hε)

lemma integrable_quadraticDamping_nonneg {μ : Measure (Space n)} [IsFiniteMeasure μ]
    {f : Space n → ℝ} (hf : Integrable f μ) {ε : ℝ} (hε : 0 ≤ ε) :
    Integrable f (quadraticDamping μ ε) := by
  rw [quadraticDamping, integrable_tilted_iff (integrable_exp_quadraticDamping μ hε)]
  simpa only [smul_eq_mul, mul_comm] using hf.mul_bdd (by fun_prop)
    (Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
        exp_quadraticDamping_le_one hε x)

theorem tendsto_integral_quadraticDamping_nonneg
    (μ : Measure (Space n)) [IsProbabilityMeasure μ] {f : Space n → ℝ}
    (hf : Integrable f μ) {ε : ℕ → ℝ} (hε : ∀ k, 0 ≤ ε k)
    (hεlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, f x ∂quadraticDamping μ (ε k)) atTop (𝓝 (∫ x, f x ∂μ)) := by
  have hnum := tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
    (F := fun k x => f x * Real.exp (-ε k * ‖x‖ ^ 2)) (f := f)
    (fun k => hf.aestronglyMeasurable.mul (by fun_prop)) hf.norm
    (fun k => Eventually.of_forall fun x => by
      simp only [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact mul_le_of_le_one_right (abs_nonneg _) (exp_quadraticDamping_le_one (hε k) x))
    (Eventually.of_forall fun x => by
      have he := ((Real.continuous_exp.tendsto 0).comp
        (by simpa using hεlim.neg.mul_const (‖x‖ ^ 2))).const_mul (f x)
      simpa only [Real.exp_zero, mul_one, Function.comp_def, neg_mul] using he)
  have hden := tendsto_integral_of_dominated_convergence (fun _ : Space n => (1 : ℝ))
    (F := fun k x => Real.exp (-ε k * ‖x‖ ^ 2)) (f := fun _ => (1 : ℝ)) (μ := μ)
    (fun _ => by fun_prop) (integrable_const _)
    (fun k => Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
        exp_quadraticDamping_le_one (hε k) x)
    (Eventually.of_forall fun x => by
      simpa only [Real.exp_zero, Function.comp_def] using
        (Real.continuous_exp.tendsto 0).comp
          (by simpa using hεlim.neg.mul_const (‖x‖ ^ 2)))
  have he (k : ℕ) : (∫ x, f x ∂quadraticDamping μ (ε k)) =
      (∫ x, f x * Real.exp (-ε k * ‖x‖ ^ 2) ∂μ) /
        (∫ x, Real.exp (-ε k * ‖x‖ ^ 2) ∂μ) :=
    tiltAverage_eq_ratio μ _ _
  simp_rw [he]
  simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul, div_one, Pi.div_def] using
    hnum.div hden (by simp : (∫ _ : Space n, (1 : ℝ) ∂μ) ≠ 0)

end KLS
end

import KLS.NormExponentialDomain

/-! A single radial exponential rate supplies a local tilt domain. This
definition does not require exponential moments at every positive rate. -/

open MeasureTheory InnerProductSpace Set Filter Metric
open scoped ContDiff Topology
noncomputable section
namespace KLS
variable {n : ℕ}

def LocalNormExponentialDomain (μ : Measure (Space n)) (f : Space n → ℝ) (r : ℝ) : Prop :=
  AEStronglyMeasurable f μ ∧ ∀ m : ℕ,
    Integrable (fun x => ‖f x‖ * ‖x‖ ^ m * Real.exp (r * ‖x‖)) μ

theorem NormExponentialDomain.local {μ : Measure (Space n)} {f : Space n → ℝ}
    (hf : NormExponentialDomain μ f) (r : ℝ) : LocalNormExponentialDomain μ f r :=
  ⟨hf.1, fun m => hf.2 m r⟩

theorem LocalNormExponentialDomain.mul_coordinate {μ : Measure (Space n)}
    {f : Space n → ℝ} {r : ℝ} (hf : LocalNormExponentialDomain μ f r) (i : Fin n) :
    LocalNormExponentialDomain μ (fun x => f x * x i) r := by
  refine ⟨hf.1.mul ((show Continuous (fun x : Space n => x i) by fun_prop).aestronglyMeasurable), ?_⟩
  intro m
  apply (hf.2 (m + 1)).mono' (((hf.1.mul
    (show Continuous (fun x : Space n => x i) by fun_prop).aestronglyMeasurable).norm.mul
    (continuous_norm.pow m).aestronglyMeasurable).mul
    (show Continuous (fun x : Space n => Real.exp (r * ‖x‖)) by fun_prop).aestronglyMeasurable)
  filter_upwards [] with x
  change ‖‖f x * x i‖ * ‖x‖ ^ m * Real.exp (r * ‖x‖)‖ ≤
    ‖f x‖ * ‖x‖ ^ (m + 1) * Real.exp (r * ‖x‖)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_mul]
  have hx : ‖x i‖ ≤ ‖x‖ := PiLp.norm_apply_le x i
  calc
    _ ≤ ‖f x‖ * ‖x‖ * ‖x‖ ^ m * Real.exp (r * ‖x‖) := by gcongr
    _ = _ := by rw [pow_succ]; ring

theorem LocalNormExponentialDomain.integrable_tilt {μ : Measure (Space n)}
    {f : Space n → ℝ} {r : ℝ} (hf : LocalNormExponentialDomain μ f r)
    {w : Space n} (hw : ‖w‖ ≤ r) :
    Integrable (fun x => f x * Real.exp (inner ℝ w x)) μ := by
  apply (hf.2 0).mono'
    (hf.1.mul (show Continuous (fun x : Space n => Real.exp (inner ℝ w x)) by fun_prop).aestronglyMeasurable)
  filter_upwards [] with x
  change ‖f x * Real.exp (inner ℝ w x)‖ ≤ ‖f x‖ * ‖x‖ ^ 0 * Real.exp (r * ‖x‖)
  simp only [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), pow_zero, mul_one]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg (f x))
  exact (exp_inner_le_exp_norm w x).trans
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hw (norm_nonneg x)))

theorem LocalNormExponentialDomain.integrable_tilt_derivative {μ : Measure (Space n)}
    {f : Space n → ℝ} {r : ℝ} (hf : LocalNormExponentialDomain μ f r)
    {w : Space n} (hw : ‖w‖ ≤ r) :
    Integrable (fun x => (f x * Real.exp (inner ℝ w x)) • innerSL ℝ x) μ := by
  apply (hf.2 1).mono' ((hf.1.mul
    (show Continuous (fun x : Space n => Real.exp (inner ℝ w x)) by fun_prop).aestronglyMeasurable).smul
    (show Continuous (fun x : Space n => innerSL ℝ x) by fun_prop).aestronglyMeasurable)
  filter_upwards [] with x
  change ‖(f x * Real.exp (inner ℝ w x)) • innerSL ℝ x‖ ≤
    ‖f x‖ * ‖x‖ ^ 1 * Real.exp (r * ‖x‖)
  simp only [norm_smul, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), pow_one]
  rw [innerSL_apply_norm]
  have he : Real.exp (inner ℝ w x) ≤ Real.exp (r * ‖x‖) :=
    (exp_inner_le_exp_norm w x).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hw (norm_nonneg x)))
  calc
    _ ≤ |f x| * Real.exp (r * ‖x‖) * ‖x‖ := by gcongr
    _ = _ := by ring

end KLS
end

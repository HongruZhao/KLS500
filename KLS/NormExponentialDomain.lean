import KLS.WeightedNormExponential
import KLS.TiltFrechet

/-! A concrete exponential-moment domain, stable under multiplication by
coordinates. The weighted L² domain lies in it by proved radial domination. -/

open MeasureTheory InnerProductSpace Set Filter Metric Matrix
open scoped ContDiff RealInnerProductSpace Topology

noncomputable section
namespace KLS
variable {n : ℕ}

def NormExponentialDomain (μ : Measure (Space n)) (f : Space n → ℝ) : Prop :=
  AEStronglyMeasurable f μ ∧ ∀ (m : ℕ) (a : ℝ),
    Integrable (fun x => ‖f x‖ * ‖x‖ ^ m * Real.exp (a * ‖x‖)) μ

theorem normExponentialDomain_of_memLp_potentialMeasure
    {φ f : Space n → ℝ} {κ : ℝ}
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ y (v : Fin n → ℝ),
      κ * (v ⬝ᵥ v) ≤ v ⬝ᵥ (coordinateHessian φ y *ᵥ v))
    (hf : MemLp f 2 (potentialMeasure φ)) : NormExponentialDomain (potentialMeasure φ) f :=
  ⟨hf.aestronglyMeasurable, integrable_abs_mul_norm_pow_exp_norm_of_memLp hφ hκ hlower hf⟩

theorem exp_inner_le_exp_norm (w x : Space n) :
    Real.exp (inner ℝ w x) ≤ Real.exp (‖w‖ * ‖x‖) :=
  Real.exp_le_exp.mpr (real_inner_le_norm w x)

theorem NormExponentialDomain.mul_coordinate {μ : Measure (Space n)} {f : Space n → ℝ}
    (hf : NormExponentialDomain μ f) (i : Fin n) :
    NormExponentialDomain μ (fun x => f x * x i) := by
  refine ⟨hf.1.mul ((show Continuous (fun x : Space n => x i) by fun_prop).aestronglyMeasurable), ?_⟩
  intro m a
  apply (hf.2 (m + 1) a).mono' (((hf.1.mul
    (show Continuous (fun x : Space n => x i) by fun_prop).aestronglyMeasurable).norm.mul
    (continuous_norm.pow m).aestronglyMeasurable).mul
    (show Continuous (fun x : Space n => Real.exp (a * ‖x‖)) by fun_prop).aestronglyMeasurable)
  filter_upwards [] with x
  change ‖‖f x * x i‖ * ‖x‖ ^ m * Real.exp (a * ‖x‖)‖ ≤
    ‖f x‖ * ‖x‖ ^ (m + 1) * Real.exp (a * ‖x‖)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_mul]
  have hx : ‖x i‖ ≤ ‖x‖ := PiLp.norm_apply_le x i
  calc
    _ ≤ ‖f x‖ * ‖x‖ * ‖x‖ ^ m * Real.exp (a * ‖x‖) := by gcongr
    _ = _ := by rw [pow_succ]; ring

theorem NormExponentialDomain.integrable_tilt {μ : Measure (Space n)} {f : Space n → ℝ}
    (hf : NormExponentialDomain μ f) (w : Space n) :
    Integrable (fun x => f x * Real.exp (inner ℝ w x)) μ := by
  apply (hf.2 0 ‖w‖).mono'
    (hf.1.mul (show Continuous (fun x : Space n => Real.exp (inner ℝ w x)) by fun_prop).aestronglyMeasurable)
  filter_upwards [] with x
  change ‖f x * Real.exp (inner ℝ w x)‖ ≤ ‖f x‖ * ‖x‖ ^ 0 * Real.exp (‖w‖ * ‖x‖)
  simp only [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), pow_zero, mul_one]
  exact mul_le_mul_of_nonneg_left (exp_inner_le_exp_norm w x) (abs_nonneg (f x))

theorem NormExponentialDomain.integrable_tilt_derivative
    {μ : Measure (Space n)} {f : Space n → ℝ}
    (hf : NormExponentialDomain μ f) (w : Space n) :
    Integrable (fun x => (f x * Real.exp (inner ℝ w x)) • innerSL ℝ x) μ := by
  apply (hf.2 1 ‖w‖).mono' ((hf.1.mul
    (show Continuous (fun x : Space n => Real.exp (inner ℝ w x)) by fun_prop).aestronglyMeasurable).smul
    (show Continuous (fun x : Space n => innerSL ℝ x) by fun_prop).aestronglyMeasurable)
  filter_upwards [] with x
  change ‖(f x * Real.exp (inner ℝ w x)) • innerSL ℝ x‖ ≤
    ‖f x‖ * ‖x‖ ^ 1 * Real.exp (‖w‖ * ‖x‖)
  simp only [norm_smul, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), pow_one]
  rw [innerSL_apply_norm]
  calc
    _ ≤ |f x| * Real.exp (‖w‖ * ‖x‖) * ‖x‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (exp_inner_le_exp_norm w x) (abs_nonneg _)) (norm_nonneg _)
    _ = _ := by ring

end KLS
end

#print axioms KLS.normExponentialDomain_of_memLp_potentialMeasure
#print axioms KLS.NormExponentialDomain.mul_coordinate
#print axioms KLS.NormExponentialDomain.integrable_tilt_derivative

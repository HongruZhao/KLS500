import KLS.WeightedDiffusionSquare

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology ContDiff ENNReal RealInnerProductSpace

noncomputable section
namespace KLS
variable {n : ℕ}

theorem gradient_add_real {f g : Space n → ℝ} {x : Space n}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    gradient (f+g) x=gradient f x+gradient g x := by
  ext i
  rw [← coordinateDerivative_eq_gradient,coordinateDerivative_add hf hg]
  simp only [PiLp.add_apply,coordinateDerivative_eq_gradient]

theorem gradient_smul_real {f : Space n → ℝ} {x : Space n}
    (hf : DifferentiableAt ℝ f x) (c : ℝ) :
    gradient (c • f) x=c • gradient f x := by
  ext i
  rw [← coordinateDerivative_eq_gradient,coordinateDerivative_smul hf]
  simp only [PiLp.smul_apply,smul_eq_mul,coordinateDerivative_eq_gradient]

theorem gradient_sq_real {f : Space n → ℝ} (hf : Differentiable ℝ f) (x : Space n) :
    gradient (fun y => f y ^ 2) x=(2*f x) • gradient f x := by
  ext i
  rw [← coordinateDerivative_eq_gradient,coordinateDerivative_sq hf]
  simp only [PiLp.smul_apply,smul_eq_mul,coordinateDerivative_eq_gradient]

/-- The actual graph coordinate derivatives give a vector-valued L2 gradient. -/
theorem memLp_gradient_of_coordinateDerivative {φ f : Space n → ℝ}
    (hf : ContDiff ℝ 1 f)
    (hd : ∀ i : Fin n, MemLp (coordinateDerivative f i) 2 (potentialMeasure φ)) :
    MemLp (gradient f) 2 (potentialMeasure φ) := by
  apply (memLp_two_iff_integrable_sq_norm
    (continuous_gradient_of_contDiff hf).aestronglyMeasurable).mpr
  exact integrable_gradient_norm_sq_of_energy_lt_top
    (energy_lt_top_of_memLp_coordinateDerivative hd)

/-- The actual square has integrable gradient under precisely L2 value and gradient. -/
theorem integrable_gradient_sq_of_memLp {φ f : Space n → ℝ}
    (hf : ContDiff ℝ 1 f) (hf2 : MemLp f 2 (potentialMeasure φ))
    (hgrad2 : MemLp (gradient f) 2 (potentialMeasure φ)) :
    Integrable (gradient (fun x => f x ^ 2)) (potentialMeasure φ) := by
  have hp := hf2.norm.integrable_mul hgrad2.norm
  apply (hp.const_mul 2).mono'
    (continuous_gradient_of_contDiff (hf.pow 2)).aestronglyMeasurable
  exact Eventually.of_forall fun x => by
    rw [gradient_sq_real (hf.differentiable one_ne_zero),norm_smul]
    simp only [Real.norm_eq_abs,abs_mul,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    simp only [Pi.mul_apply]
    ring_nf
    exact le_rfl

end KLS
end

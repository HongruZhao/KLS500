import KLS.WeightedSubsolutionMaximum

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology ContDiff ENNReal RealInnerProductSpace

noncomputable section
namespace KLS
variable {n : ℕ}

/-- Actual first derivative of a scalar square. -/
theorem coordinateDerivative_sq {f : Space n → ℝ} (hf : Differentiable ℝ f)
    (i : Fin n) (x : Space n) :
    coordinateDerivative (fun y => f y ^ 2) i x = 2*f x*coordinateDerivative f i x := by
  simp only [pow_two]
  rw [coordinateDerivative_mul (hf x) (hf x)]
  ring

/-- The literal product rule for the weighted diffusion of a square. -/
theorem weightedDiffusion_sq (φ : Space n → ℝ) {f : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) (x : Space n) :
    weightedDiffusion φ (fun y => f y ^ 2) x =
      2*f x*weightedDiffusion φ f x+2*‖gradient f x‖ ^ 2 := by
  have hη : ContDiff ℝ 2 (fun z : ℝ => z ^ 2) := contDiff_id.pow 2
  have hder : deriv (fun z : ℝ => z ^ 2) = fun z => 2*z := by
    funext z
    simp only [deriv_pow_field,Nat.cast_ofNat,Nat.add_one_sub_one,pow_one]
  have hder2 (z : ℝ) : deriv (fun y : ℝ => 2*y) z=2 := by simp
  rw [weightedDiffusion_eq_sum,weightedDiffusion_eq_sum,
    ← real_inner_self_eq_norm_sq,← sum_coordinateDerivative_mul,
    Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [coordinateHessian_scalar_comp hη hf,coordinateDerivative_sq (hf.differentiable (by norm_num)),
    hder,hder2]
  ring

end KLS
end

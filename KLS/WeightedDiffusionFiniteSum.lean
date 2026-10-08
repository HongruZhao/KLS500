import KLS.WeightedResolventVariance

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology ContDiff ENNReal RealInnerProductSpace

noncomputable section
namespace KLS
variable {n : ℕ}

/-- Actual gradients commute with a finite sum of differentiable functions. -/
theorem gradient_fintype_sum_real {α : Type*} [Fintype α]
    {f : α → Space n → ℝ} (hf : ∀ a, Differentiable ℝ (f a)) (x : Space n) :
    gradient (fun y => ∑ a, f a y) x=∑ a, gradient (f a) x := by
  ext i
  rw [← coordinateDerivative_eq_gradient,coordinateDerivative_sum (fun a => hf a x)]
  simp only [coordinateDerivative_eq_gradient]
  exact (map_sum (EuclideanSpace.proj i : Space n →L[ℝ] ℝ)
    (fun a => gradient (f a) x) Finset.univ).symm

/-- Actual coordinate Hessians commute with a finite sum. -/
theorem coordinateHessian_fintype_sum {α : Type*} [Fintype α]
    {f : α → Space n → ℝ} (hf : ∀ a, ContDiff ℝ 2 (f a))
    (x : Space n) (i j : Fin n) :
    coordinateHessian (fun y => ∑ a, f a y) x i j=∑ a, coordinateHessian (f a) x i j := by
  have he : coordinateDerivative (fun y => ∑ a, f a y) j =
      fun y => ∑ a, coordinateDerivative (f a) j y := by
    funext y
    exact coordinateDerivative_sum (fun a => (hf a).differentiable (by norm_num) y) j
  change coordinateDerivative (coordinateDerivative (fun y => ∑ a, f a y) j) i x = _
  rw [he,coordinateDerivative_sum (fun a =>
    (contDiff_coordinateDerivative (hf a) (m := 1) (by norm_num) j).differentiable one_ne_zero x)]
  rfl

/-- The concrete weighted diffusion commutes with a finite sum. -/
theorem weightedDiffusion_fintype_sum {α : Type*} [Fintype α]
    (φ : Space n → ℝ) {f : α → Space n → ℝ}
    (hf : ∀ a, ContDiff ℝ 2 (f a)) (x : Space n) :
    weightedDiffusion φ (fun y => ∑ a, f a y) x=∑ a, weightedDiffusion φ (f a) x := by
  simp_rw [weightedDiffusion_eq_sum,coordinateHessian_fintype_sum hf,
    coordinateDerivative_sum (fun a => (hf a).differentiable (by norm_num) x),
    Finset.sum_mul,← Finset.sum_sub_distrib]
  exact Finset.sum_comm

end KLS
end

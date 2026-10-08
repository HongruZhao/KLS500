import KLS.PointwiseWeightedBochner

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology ContDiff ENNReal RealInnerProductSpace

noncomputable section
namespace KLS
variable {n : ℕ}

/-- The actual squared gradient has an integrable vector gradient whenever
the coordinate gradient and Hessian are square integrable. -/
theorem integrable_gradient_gradient_norm_sq {φ f : Space n → ℝ}
    (hf : ContDiff ℝ 2 f)
    (hd : ∀ i : Fin n, MemLp (coordinateDerivative f i) 2 (potentialMeasure φ))
    (hH : Integrable (hessianSquare f) (potentialMeasure φ)) :
    Integrable (gradient (fun x => ‖gradient f x‖ ^ 2)) (potentialMeasure φ) := by
  have hdi (i : Fin n) : ContDiff ℝ 1 (coordinateDerivative f i) :=
    contDiff_coordinateDerivative hf (by norm_num) i
  have hsq : (fun y => ‖gradient f y‖ ^ 2) = fun y => ∑ i, coordinateDerivative f i y ^ 2 := by
    funext y
    simp only [EuclideanSpace.real_norm_sq_eq,coordinateDerivative_eq_gradient]
  have hgrad : gradient (fun y => ∑ i, coordinateDerivative f i y ^ 2) =
      fun y => ∑ i, gradient (fun z => coordinateDerivative f i z ^ 2) y := by
    funext y
    exact gradient_fintype_sum_real (fun i => ((hdi i).pow 2).differentiable one_ne_zero) y
  rw [hsq,hgrad]
  apply integrable_finsetSum Finset.univ
  intro i _
  apply integrable_gradient_sq_of_memLp (hdi i) (hd i)
  apply memLp_gradient_of_coordinateDerivative (hdi i)
  intro j
  exact memLp_coordinateHessian_of_integrable_hessianSquare hf hH j i

end KLS
end

import KLS.ConvexPeanoHessian

open Matrix Set Filter Metric InnerProductSpace Asymptotics
open scoped Topology BigOperators Matrix.Norms.Elementwise
noncomputable section
namespace KLS
variable {n : ℕ}

lemma coordinateHessian_eq_of_hasFDerivAt_gradient
    {u : Space n → ℝ} {x : Space n} {H : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.IsSymm) (hu : HasFDerivAt (gradient u) (matrixAction H) x) :
    coordinateHessian u x = H := by
  ext i j
  have heq : coordinateDerivative u j = fun y : Space n => (gradient u y) j := by
    funext y
    exact coordinateDerivative_eq_gradient u j y
  change coordinateDerivative (coordinateDerivative u j) i x = H i j
  rw [heq]
  have hd : HasFDerivAt (fun y : Space n => (gradient u y) j)
      ((EuclideanSpace.proj (𝕜 := ℝ) j).comp (matrixAction H)) x :=
    (EuclideanSpace.proj (𝕜 := ℝ) j).hasFDerivAt.comp x hu
  rw [coordinateDerivative, hd.fderiv]
  change (matrixAction H (EuclideanSpace.single i 1)) j = H i j
  simp only [matrixAction_apply, PiLp.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact hH.apply i j

/-- The actual coordinate Hessian exists as the derivative of the actual
gradient at the initialized point and satisfies the normalized nonlinear
equation there. No second derivative was part of the input data. -/
theorem weighted_second_derivative_at_initialized_center (hn : 0 < n) {α : ℝ} (hα : 0 < α) :
    ∃ Δ : ℝ, 0 < Δ ∧
      ∀ d₀ : NormalizedWeightedMomentData n 1 1, d₀.epsilon < Δ →
      (∀ x ∈ closedBall (0 : Space n) 1,
        |weightedDataDensity d₀ x - 1| ≤ d₀.epsilon ^ 2 * ‖x‖ ^ α) →
      (coordinateHessian d₀.u 0).PosDef ∧ (coordinateHessian d₀.u 0).det = 1 ∧
        HasFDerivAt (gradient d₀.u) (matrixAction (coordinateHessian d₀.u 0)) 0 := by
  obtain ⟨Δ, hΔ, hderiv⟩ := weighted_exists_gradient_derivative hn hα
  refine ⟨Δ, hΔ, ?_⟩
  intro d₀ hd hholder
  obtain ⟨H, hHpos, hHdet, hderiv⟩ := hderiv d₀ hd hholder
  have heq := coordinateHessian_eq_of_hasFDerivAt_gradient hHpos.isHermitian.isSymm hderiv
  rw [heq]
  exact ⟨hHpos, hHdet, hderiv⟩

end KLS
end

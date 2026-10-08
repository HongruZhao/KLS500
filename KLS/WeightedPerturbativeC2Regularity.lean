import KLS.UniformInnerQuadraticFamily

open MeasureTheory Matrix Set Filter Metric InnerProductSpace Asymptotics
open scoped Topology BigOperators Matrix.Norms.Elementwise NNReal
noncomputable section
namespace KLS
variable {n : ℕ}

/-- Genuine local C2 regularity from one actual near-quadratic weak weighted
moment datum and a small full Holder modulus of its actual density. The
neighborhood family and every central initializer are derived, and the
actual coordinate Hessian satisfies the nonlinear determinant equation. -/
theorem weighted_perturbative_c2_regularity (hn : 0 < n) {α : ℝ} (hα : 0 < α) :
    ∃ Δ : ℝ, 0 < Δ ∧
      ∀ d₀ : NormalizedWeightedMomentData n 1 1, d₀.epsilon < Δ →
      (∀ x ∈ closedBall (0 : Space n) 1, ∀ y ∈ closedBall (0 : Space n) 1,
        |weightedDataDensity d₀ x - weightedDataDensity d₀ y| ≤ d₀.epsilon ^ 2 * ‖x - y‖ ^ α) →
      ContDiffOn ℝ 2 d₀.u (ball (0 : Space n) (1 / 4)) ∧
        ∀ c ∈ ball (0 : Space n) (1 / 4),
          (coordinateHessian d₀.u c).PosDef ∧
          (coordinateHessian d₀.u c).det = weightedDataDensity d₀ c := by
  obtain ⟨r, β, C, Δ, hr, hrone, hβ, hβone, hC, hΔ, hfamily⟩ :=
    weighted_exists_uniform_inner_quadratic_family hn hα
  refine ⟨Δ, hΔ, ?_⟩
  intro d₀ hd hholder
  obtain ⟨H, hH, hb⟩ := hfamily d₀ hd hholder
  have hu := d₀.contDiff.differentiable (by norm_num)
  have hD : 0 ≤ C * d₀.epsilon := mul_nonneg hC.le d₀.epsilon_pos.le
  have hsym (c : Space n) (hc : c ∈ ball (0 : Space n) (1 / 4)) : (H c).IsSymm :=
    (hH c (ball_subset_closedBall hc)).1.isHermitian.isSymm
  have hbound : ∀ c ∈ ball (0 : Space n) (1 / 4), ∀ (j : ℕ) (x : Space n),
      ‖x - c‖ ≤ (1 / 8 : ℝ) * r ^ j / 2 →
      |d₀.u x - centeredQuadratic (H c) c (gradient d₀.u c) (d₀.u c) x| ≤
        (C * d₀.epsilon) * β ^ j * r ^ (2 * j) := by
    intro c hc j x hx
    exact hb c (ball_subset_closedBall hc) j x (hx.trans_eq (by ring))
  refine ⟨contDiffOn_two_of_uniform_scaled_geometric_taylor hu d₀.strictConvex.convexOn
    isOpen_ball hsym hD (by norm_num : (0 : ℝ) < 1 / 8) hr hrone hβ hβone hbound, ?_⟩
  intro c hc
  have hderiv := hasFDerivAt_gradient_of_scaled_geometric_taylor hu d₀.strictConvex.convexOn
    (hsym c hc) hD (by norm_num : (0 : ℝ) < 1 / 8) hr hrone hβ hβone (hbound c hc)
  have heq := coordinateHessian_eq_of_hasFDerivAt_gradient (hsym c hc) hderiv
  rw [heq]
  exact hH c (ball_subset_closedBall hc)

end KLS
end

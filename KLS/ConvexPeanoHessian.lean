import KLS.ConvexQuadraticGradientBound

open Matrix Set Filter Metric InnerProductSpace Asymptotics
open scoped Topology BigOperators Matrix.Norms.Elementwise
noncomputable section
namespace KLS
variable {n : ℕ}

/-- Convexity supplies the missing implication from a second-order Peano
expansion to differentiability of the actual gradient. No Hessian of the
original function is assumed. -/
theorem convex_hasFDerivAt_gradient_of_second_order_small
    {u : Space n → ℝ} (hu : Differentiable ℝ u) (huc : ConvexOn ℝ univ u)
    {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsSymm)
    (hsmall : ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ x : Space n, ‖x‖ < δ →
        |u x - centeredQuadratic H 0 (gradient u 0) (u 0) x| ≤ η * ‖x‖ ^ 2) :
    HasFDerivAt (gradient u) (matrixAction H) 0 := by
  apply hasFDerivAt_iff_isLittleO.mpr
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  let t := min 1 (ε / (‖matrixAction H‖ + 1))
  have ht : 0 < t := lt_min (by norm_num) (by positivity)
  have htone : t ≤ 1 := min_le_left _ _
  have htbound : t * ‖matrixAction H‖ ≤ ε := by
    have hh := (le_div_iff₀ (by positivity : 0 < ‖matrixAction H‖ + 1)).mp
      (show t ≤ ε / (‖matrixAction H‖ + 1) from min_le_right _ _)
    nlinarith
  have hη : 0 < ε * t / 10 := by positivity
  obtain ⟨δ, hδ, hb⟩ := hsmall (ε * t / 10) hη
  have hcoef : 5 * (ε * t / 10) / t + t / 2 * ‖matrixAction H‖ ≤ ε := by
    have hh : 5 * (ε * t / 10) / t = ε / 2 := by field_simp; ring
    rw [hh]
    linarith
  filter_upwards [Metric.ball_mem_nhds (0 : Space n) (show 0 < δ / 2 by positivity)] with x hx
  have hx' : ‖x‖ < δ / 2 := by simpa only [mem_ball_zero_iff] using hx
  by_cases hxzero : x = 0
  · simp only [hxzero, sub_self, map_zero, norm_zero, mul_zero, le_refl]
  have hlocal : ∀ y : Space n, ‖y‖ ≤ 2 * ‖x‖ →
      |u y - centeredQuadratic H 0 (gradient u 0) (u 0) y| ≤ (ε * t / 10) * ‖y‖ ^ 2 := by
    intro y hy
    exact hb y (by linarith)
  have hh := norm_gradient_sub_quadratic_le huc hH (hu x) hxzero hη.le ht htone hlocal
  have heq : gradient u x - gradient u 0 - matrixAction H (x - 0) =
      gradient u x - (gradient u 0 + matrixAction H x) := by simp only [sub_zero]; abel
  rw [heq, sub_zero]
  exact hh.trans (mul_le_mul_of_nonneg_right hcoef (norm_nonneg x))

theorem convex_hasFDerivAt_gradient_of_quadratic_peano
    {u : Space n → ℝ} (hu : Differentiable ℝ u) (huc : ConvexOn ℝ univ u)
    {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsSymm)
    (hrem : (fun x => u x - centeredQuadratic H 0 (gradient u 0) (u 0) x)
      =o[𝓝 (0 : Space n)] (fun x => ‖x‖ ^ 2)) :
    HasFDerivAt (gradient u) (matrixAction H) 0 := by
  apply convex_hasFDerivAt_gradient_of_second_order_small hu huc hH
  intro η hη
  obtain ⟨δ, hδ, hb⟩ := Metric.eventually_nhds_iff.mp (hrem.bound hη)
  refine ⟨δ, hδ, ?_⟩
  intro x hx
  have hh := hb (show dist x (0 : Space n) < δ by simpa only [dist_zero_right] using hx)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖x‖)] using hh

/-- Genuine differentiability of the actual weak weighted solution's
gradient at the initialized center, with a positive definite determinant-one
derivative. This is a pointwise conclusion from the proved perturbative data. -/
theorem weighted_exists_gradient_derivative (hn : 0 < n) {α : ℝ} (hα : 0 < α) :
    ∃ Δ : ℝ, 0 < Δ ∧
      ∀ d₀ : NormalizedWeightedMomentData n 1 1, d₀.epsilon < Δ →
      (∀ x ∈ closedBall (0 : Space n) 1,
        |weightedDataDensity d₀ x - 1| ≤ d₀.epsilon ^ 2 * ‖x‖ ^ α) →
      ∃ H : Matrix (Fin n) (Fin n) ℝ, H.PosDef ∧ H.det = 1 ∧
        HasFDerivAt (gradient d₀.u) (matrixAction H) 0 := by
  obtain ⟨Δ, hΔ, hjet⟩ := weighted_exists_quadratic_peano_jet hn hα
  refine ⟨Δ, hΔ, ?_⟩
  intro d₀ hd hholder
  obtain ⟨H, hHpos, hHdet, hrem⟩ := hjet d₀ hd hholder
  exact ⟨H, hHpos, hHdet, convex_hasFDerivAt_gradient_of_quadratic_peano
    (d₀.contDiff.differentiable (by norm_num)) d₀.strictConvex.convexOn hHpos.isHermitian.isSymm hrem⟩

end KLS
end

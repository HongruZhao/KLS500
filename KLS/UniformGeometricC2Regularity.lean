import KLS.CenteredGeometricHessian

open Matrix Set Filter Metric InnerProductSpace Asymptotics
open scoped Topology BigOperators Matrix.Norms.Elementwise
noncomputable section
namespace KLS
variable {n : ℕ}

/-- A continuous derivative matrix for the actual gradient gives ordinary
C2 regularity on an open set. -/
lemma contDiffOn_two_of_continuous_gradient_derivative
    {u : Space n → ℝ} (hu : Differentiable ℝ u)
    {H : Space n → Matrix (Fin n) (Fin n) ℝ} {S : Set (Space n)} (hS : IsOpen S)
    (hH : ContinuousOn H S)
    (hd : ∀ c ∈ S, HasFDerivAt (gradient u) (matrixAction (H c)) c) :
    ContDiffOn ℝ 2 u S := by
  have hgrad : ContDiffOn ℝ 1 (gradient u) S := by
    have hh := (contDiffOn_succ_iff_fderiv_of_isOpen (𝕜 := ℝ) (n := 0) (f := gradient u) hS)
    apply hh.mpr
    refine ⟨fun c hc => (hd c hc).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    apply contDiffOn_zero.mpr
    apply (continuous_matrixAction.comp_continuousOn hH).congr
    intro c hc
    exact (hd c hc).fderiv
  have hfd : ContDiffOn ℝ 1 (fderiv ℝ u) S := by
    rw [← toDual_comp_gradient]
    exact (toDual ℝ (Space n)).contDiff.comp_contDiffOn hgrad
  exact (contDiffOn_succ_iff_fderiv_of_isOpen (𝕜 := ℝ) (n := 1) (f := u) hS).mpr
    ⟨hu.differentiableOn, by simp, hfd⟩

/-- Uniform geometric quadratic approximation at every point of an open
set yields genuine C2 regularity of the original convex function. The uniform
neighborhood approximation family remains an explicit, necessary input. -/
theorem contDiffOn_two_of_uniform_geometric_taylor
    {u : Space n → ℝ} (hu : Differentiable ℝ u) (huc : ConvexOn ℝ univ u)
    {H : Space n → Matrix (Fin n) (Fin n) ℝ} {S : Set (Space n)} {D r β : ℝ}
    (hS : IsOpen S) (hH : ∀ c ∈ S, (H c).IsSymm)
    (hD : 0 ≤ D) (hr : 0 < r) (hrone : r < 1) (hβ : 0 ≤ β) (hβone : β < 1)
    (hb : ∀ c ∈ S, ∀ (j : ℕ) (y : Space n), ‖y - c‖ ≤ r ^ j / 2 →
      |u y - centeredQuadratic (H c) c (gradient u c) (u c) y| ≤ D * β ^ j * r ^ (2 * j)) :
    ContDiffOn ℝ 2 u S := by
  have hcontinuous := continuousOn_hessian_of_uniform_geometric_taylor hu.continuous hH hr hβ hβone hb
  apply contDiffOn_two_of_continuous_gradient_derivative hu hS hcontinuous
  intro c hc
  exact hasFDerivAt_gradient_of_centered_geometric_taylor hu huc (hH c hc)
    hD hr hrone hβ hβone (hb c hc)

end KLS
end

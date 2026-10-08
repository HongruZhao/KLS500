import KLS.RecenteredDensityBounds

open MeasureTheory Matrix Set Filter Metric InnerProductSpace Asymptotics
open scoped Topology BigOperators Matrix.Norms.Elementwise NNReal
noncomputable section
namespace KLS
variable {n : ℕ}

/-- One actual near-quadratic weighted datum with a full two-point Holder
density bound supplies every recentered normalized datum on the inner ball.
The central determinant and both coordinate-change bounds are derived. -/
theorem exists_uniform_recentered_weighted_data (hn : 0 < n)
    (d₀ : NormalizedWeightedMomentData n 1 1) (hε : d₀.epsilon ≤ 1 / 2)
    {α : ℝ} (hα : 0 < α)
    (hholder : ∀ x ∈ closedBall (0 : Space n) 1, ∀ y ∈ closedBall (0 : Space n) 1,
      |weightedDataDensity d₀ x - weightedDataDensity d₀ y| ≤ d₀.epsilon ^ 2 * ‖x - y‖ ^ α)
    (c : Space n) (hc : ‖c‖ ≤ 1 / 4) :
    ∃ (A : Matrix (Fin n) (Fin n) ℝ) (d : NormalizedWeightedMomentData n 1 1),
      A.PosDef ∧ A.det = weightedDataDensity d₀ c ∧
      ‖matrixAction (inverseSqrtMatrix A)‖ ≤ 2 ∧
      ‖matrixAction (inverseSqrtMatrix A)⁻¹‖ ≤ 2 ∧
      d.epsilon = 32 * d₀.epsilon ∧ d.c = 0 ∧
      d.u = quadraticallyRescaledPotential d₀.u c c
        (centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 d₀.c c) (1 / 4) ∘
          matrixAction (inverseSqrtMatrix A) ∧
      (∀ y, weightedDataDensity d y =
        weightedDataDensity d₀ (c + (1 / 4 : ℝ) • matrixAction (inverseSqrtMatrix A) y) / A.det) ∧
      (∀ y ∈ closedBall (0 : Space n) 1,
        |weightedDataDensity d y - 1| ≤ d.epsilon ^ 2 * ‖y‖ ^ α) := by
  obtain ⟨A, hA, hdet, hclose, hB, hBinv⟩ := exists_recentered_density_calibration hn d₀ hε hc
  have hsmall : d₀.epsilon ≤ 1 := by linarith
  have hflat := recentered_quadratic_flatness d₀ hsmall hclose hc
  have hflat' : ∀ x ∈ closedBall c (1 / 2),
      |d₀.u x - centeredQuadratic A c c
        (centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 d₀.c c) x| ≤
          (32 * d₀.epsilon) * (1 / 4 : ℝ) ^ 2 := by
    intro x hx
    exact (hflat x hx).trans_eq (by ring)
  have hdensity := recentered_normalized_density_holder d₀ hε hα hholder hdet hB hc
  have huniform : ∀ y ∈ closedBall (0 : Space n) 1,
      |weightedDataDensity d₀ (c + (1 / 4 : ℝ) • matrixAction (inverseSqrtMatrix A) y) / A.det - 1| ≤
        (32 * d₀.epsilon) ^ 2 := by
    intro y hy
    have hyn : ‖y‖ ≤ 1 := by simpa only [mem_closedBall_zero_iff] using hy
    have hp : ‖y‖ ^ α ≤ 1 := Real.rpow_le_one (norm_nonneg _) hyn hα.le
    exact (hdensity y hy).trans (mul_le_of_le_one_right (sq_nonneg _) hp)
  obtain ⟨d, hdε, hdc, hdu, hddensity⟩ := exists_centered_whitened_weighted_data
    d₀.lipschitz d₀.contDiff d₀.strictConvex d₀.continuous_source d₀.continuous_target
    d₀.closed_target d₀.convex_target d₀.pushforward hA c c
    (centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 d₀.c c)
    (by norm_num : (0 : ℝ) < 1 / 4) (mul_pos (by norm_num) d₀.epsilon_pos)
    (by linarith : (1 / 4 : ℝ) * ‖matrixAction (inverseSqrtMatrix A)‖ ≤ 1 / 2)
    hflat' huniform
  refine ⟨A, d, hA, hdet, hB, hBinv, hdε, hdc, hdu, hddensity, ?_⟩
  intro y hy
  rw [hddensity y, hdε]
  exact hdensity y hy

end KLS
end

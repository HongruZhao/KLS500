import KLS.WeightedRescaledWhitenedData
import KLS.WhiteningProductBounds

open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff NNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

/-- One actual successor in the normalized weighted class. The new density
bound on the smaller physical ball remains explicit; the old density bound
alone does not imply it. The coordinate map, new unknown, and new density
are all identified rather than abstractly postulated. -/
theorem weighted_improvement_successor (hn : 0 < n) :
    ∃ ρ δ Q : ℝ, 0 < ρ ∧ ρ ≤ 1 / 512 ∧ 0 < δ ∧ 0 < Q ∧
      ∀ d : NormalizedWeightedMomentData n 1 1, d.epsilon < δ →
      ∀ β : ℝ, 1 / 2 ≤ β → β < 1 →
      (∀ x ∈ closedBall (0 : Space n) ρ,
        |Real.exp (-d.W x + d.V (gradient d.u x)) - 1| ≤ (β * d.epsilon) ^ 2) →
      ∃ (A : Matrix (Fin n) (Fin n) ℝ) (p : Space n) (a : ℝ)
        (g : NormalizedWeightedMomentData n 1 1),
        A.PosDef ∧ A.det = 1 ∧ ‖matrixAction (A - 1)‖ ≤ Q * d.epsilon ∧
        ‖p‖ ≤ Q * d.epsilon ∧ |a - d.c| ≤ Q * d.epsilon ∧
        ‖matrixAction (inverseSqrtMatrix A)‖ ≤ 2 ∧
        g.epsilon = β * d.epsilon ∧ g.c = 0 ∧
        g.u = quadraticallyRescaledPotential d.u 0 p a (ρ / 2) ∘ matrixAction (inverseSqrtMatrix A) ∧
        ∀ y, Real.exp (-g.W y + g.V (gradient g.u y)) =
          Real.exp (-d.W ((ρ / 2) • matrixAction (inverseSqrtMatrix A) y) +
            d.V (gradient d.u ((ρ / 2) • matrixAction (inverseSqrtMatrix A) y))) := by
  obtain ⟨ρ, δ₀, Q, hρ, hρbound, hδ₀, hQ, himprove⟩ :=
    weighted_one_step_improvement_with_coefficients hn (T := 1) (M := 1) (θ := 1 / 8)
      (by norm_num) (by norm_num) (by norm_num)
  let δ := min δ₀ ((1 / 2) / Q)
  have hδ : 0 < δ := lt_min hδ₀ (by positivity)
  refine ⟨ρ, δ, Q, hρ, hρbound, hδ, hQ, ?_⟩
  intro d hd β hβ _hβone hdensity
  have hd₀ : d.epsilon < δ₀ := hd.trans_le (min_le_left _ _)
  have hsmall : Q * d.epsilon ≤ 1 / 2 := by
    have hh := (le_div_iff₀ hQ).mp (hd.le.trans (min_le_right _ _))
    linarith
  obtain ⟨A, p, a, hA, hdet, hAi, hp, ha, hflat⟩ := himprove d hd₀
  have hBn := (norm_inverseSqrtMatrix_action_le hA (mul_nonneg hQ.le d.epsilon_pos.le) hsmall hAi).trans
    (show 1 + 2 * (Q * d.epsilon) ≤ 2 by linarith)
  have hr : 0 < ρ / 2 := by positivity
  have hε : 0 < β * d.epsilon := mul_pos (by linarith) d.epsilon_pos
  have hmap : (ρ / 2) * ‖matrixAction (inverseSqrtMatrix A)‖ ≤ ρ := by
    have hh := mul_le_mul_of_nonneg_left hBn hr.le
    linarith
  have hflat' : ∀ x ∈ closedBall (0 : Space n) ρ,
      |d.u x - centeredQuadratic A 0 p a x| ≤ (β * d.epsilon) * (ρ / 2) ^ 2 := by
    intro x hx
    calc
      _ ≤ (1 / 8) * d.epsilon * ρ ^ 2 := hflat x hx
      _ = ((1 / 2) * d.epsilon) * (ρ / 2) ^ 2 := by ring
      _ ≤ (β * d.epsilon) * (ρ / 2) ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hβ d.epsilon_pos.le) (sq_nonneg _)
  obtain ⟨g, hgε, hgc, hgu, hgden⟩ := exists_rescaled_whitened_weighted_data
    d.lipschitz d.contDiff d.strictConvex d.continuous_source d.continuous_target
    d.closed_target d.convex_target d.pushforward hA hdet p a hr hε hmap hflat' hdensity
  exact ⟨A, p, a, g, hA, hdet, hAi, hp, ha, hBn, hgε, hgc, hgu, hgden⟩

end KLS
end

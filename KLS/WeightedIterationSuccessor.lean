import KLS.WeightedIterationState

open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff NNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

/-- This is the proved weighted successor statement, named only to avoid
repeating its long type during the dependent recursive construction. -/
def WeightedSuccessorProperty (n : ℕ) (ρ δ Q : ℝ) : Prop :=
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
          d.V (gradient d.u ((ρ / 2) • matrixAction (inverseSqrtMatrix A) y)))

/-- The original Holder modulus discharges the smaller density requirement
at every finite state. The actual successor supplies every new analytic datum. -/
theorem WeightedIterationState.exists_successor
    {d₀ : NormalizedWeightedMomentData n 1 1} {ρ δ Q β α : ℝ} {j : ℕ}
    (s : WeightedIterationState d₀ ρ Q β j)
    (hstep : WeightedSuccessorProperty n ρ δ Q)
    (hρ : 0 < ρ) (hρsmall : 2 * ρ < 1) (hQ : 0 ≤ Q)
    (hβhalf : 1 / 2 ≤ β) (hβone : β < 1) (hα : 0 < α)
    (hcompatible : (2 * ρ) ^ α ≤ β ^ 2)
    (hsmall : d₀.epsilon < δ) (hhalf : Q * d₀.epsilon ≤ 1 / 2)
    (hbudget : Real.exp (2 * Q * d₀.epsilon / (1 - β)) ≤ 2)
    (hholder : ∀ x ∈ closedBall (0 : Space n) 1,
      |weightedDataDensity d₀ x - 1| ≤ d₀.epsilon ^ 2 * ‖x‖ ^ α) :
    ∃ t : WeightedIterationState d₀ ρ Q β (j + 1), Nonempty (WeightedIterationLink s t) := by
  have hβ : 0 ≤ β := by linarith
  have heps := s.epsilon_le hβ hβone.le
  have hdensity := s.next_density_bound hQ hβ hβone hbudget hα hρ hρsmall hcompatible hholder
  obtain ⟨A, p, a, g, hA, hdet, hAi, hp, ha, _hBn, hgε, hgc, hgu, hgden⟩ :=
    hstep s.data (heps.trans_lt hsmall) β hβhalf hβone hdensity
  let B := inverseSqrtMatrix A
  have hcurrent : Q * s.data.epsilon ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left heps hQ).trans hhalf
  have hBn := norm_inverseSqrtMatrix_action_le hA (mul_nonneg hQ s.data.epsilon_pos.le) hcurrent hAi
  have hBin := norm_inverse_inverseSqrtMatrix_action_le hA (mul_nonneg hQ s.data.epsilon_pos.le) hAi
  have hforward : ‖matrixAction (s.frame * B)‖ ≤
      Real.exp (2 * Q * d₀.epsilon * ∑ k ∈ Finset.range (j + 1), β ^ k) := by
    have hbexp : ‖matrixAction B‖ ≤ Real.exp (2 * Q * s.data.epsilon) := by
      apply hBn.trans
      convert Real.add_one_le_exp (2 * Q * s.data.epsilon) using 1
      ring
    calc
      _ ≤ ‖matrixAction s.frame‖ * ‖matrixAction B‖ := norm_matrixAction_mul_le _ _
      _ ≤ Real.exp (2 * Q * d₀.epsilon * ∑ k ∈ Finset.range j, β ^ k) *
          Real.exp (2 * Q * s.data.epsilon) :=
        mul_le_mul s.frame_bound hbexp (norm_nonneg _) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add, Finset.sum_range_succ, s.epsilon_eq]; congr 1; ring
  have hinverse : ‖matrixAction ((s.frame * B)⁻¹)‖ ≤
      Real.exp (Q * d₀.epsilon * ∑ k ∈ Finset.range (j + 1), β ^ k) := by
    have hbexp : ‖matrixAction B⁻¹‖ ≤ Real.exp (Q * s.data.epsilon) := by
      apply hBin.trans
      simpa only [add_comm] using Real.add_one_le_exp (Q * s.data.epsilon)
    rw [Matrix.mul_inv_rev]
    calc
      _ ≤ ‖matrixAction B⁻¹‖ * ‖matrixAction s.frame⁻¹‖ := norm_matrixAction_mul_le _ _
      _ ≤ Real.exp (Q * s.data.epsilon) * Real.exp (Q * d₀.epsilon * ∑ k ∈ Finset.range j, β ^ k) :=
        mul_le_mul hbexp s.inverse_bound (norm_nonneg _) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add, Finset.sum_range_succ, s.epsilon_eq]; congr 1; ring
  let t : WeightedIterationState d₀ ρ Q β (j + 1) := {
    data := g
    frame := s.frame * B
    epsilon_eq := by rw [hgε, s.epsilon_eq, pow_succ]; ring
    constant_eq := fun _ => hgc
    determinant := by rw [Matrix.det_mul, abs_mul, s.determinant,
      abs_det_inverseSqrtMatrix_of_det_one hA hdet, one_mul]
    frame_bound := hforward
    inverse_bound := hinverse
    density_eq := fun x => by
      change Real.exp (-g.W x + g.V (gradient g.u x)) = _
      rw [hgden]
      change weightedDataDensity s.data ((ρ / 2) • matrixAction B x) = _
      rw [s.density_eq]
      congr 1
      rw [map_smul, smul_smul, pow_succ, MomentMap.matrixAction_mul_apply] }
  refine ⟨t, ⟨?_⟩⟩
  exact {
    A := A
    p := p
    a := a
    posDef := hA
    determinant := hdet
    hessian_increment := hAi
    slope_increment := hp
    constant_increment := ha
    frame_eq := rfl
    potential_eq := hgu }

end KLS
end

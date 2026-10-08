import KLS.WeightedIterationGeometry

open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff NNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

/-- The literal real density of a normalized weighted datum. -/
def weightedDataDensity (d : NormalizedWeightedMomentData n 1 1) : Space n → ℝ :=
  fun x => Real.exp (-d.W x + d.V (gradient d.u x))

/-- A finite iteration state records the genuine weighted unknown and the
actual cumulative frame, with its original-density identity and quantitative
bounds. No regularity beyond the normalized weighted class is asserted. -/
structure WeightedIterationState (d₀ : NormalizedWeightedMomentData n 1 1)
    (ρ Q β : ℝ) (j : ℕ) where
  data : NormalizedWeightedMomentData n 1 1
  frame : Matrix (Fin n) (Fin n) ℝ
  epsilon_eq : data.epsilon = d₀.epsilon * β ^ j
  constant_eq : j ≠ 0 → data.c = 0
  determinant : |frame.det| = 1
  frame_bound : ‖matrixAction frame‖ ≤ Real.exp (2 * Q * d₀.epsilon * ∑ k ∈ Finset.range j, β ^ k)
  inverse_bound : ‖matrixAction frame⁻¹‖ ≤ Real.exp (Q * d₀.epsilon * ∑ k ∈ Finset.range j, β ^ k)
  density_eq : ∀ x, weightedDataDensity data x =
    weightedDataDensity d₀ ((ρ / 2) ^ j • matrixAction frame x)

/-- Each link records the actual improved quadratic and the exact successor
potential, so the iteration carries mathematical content beyond its bounds. -/
structure WeightedIterationLink {d₀ : NormalizedWeightedMomentData n 1 1}
    {ρ Q β : ℝ} {j : ℕ} (s : WeightedIterationState d₀ ρ Q β j)
    (t : WeightedIterationState d₀ ρ Q β (j + 1)) where
  A : Matrix (Fin n) (Fin n) ℝ
  p : Space n
  a : ℝ
  posDef : A.PosDef
  determinant : A.det = 1
  hessian_increment : ‖matrixAction (A - 1)‖ ≤ Q * s.data.epsilon
  slope_increment : ‖p‖ ≤ Q * s.data.epsilon
  constant_increment : |a - s.data.c| ≤ Q * s.data.epsilon
  frame_eq : t.frame = s.frame * inverseSqrtMatrix A
  potential_eq : t.data.u =
    quadraticallyRescaledPotential s.data.u 0 p a (ρ / 2) ∘ matrixAction (inverseSqrtMatrix A)

noncomputable def initialWeightedIterationState (d₀ : NormalizedWeightedMomentData n 1 1)
    (ρ Q β : ℝ) : WeightedIterationState d₀ ρ Q β 0 where
  data := d₀
  frame := 1
  epsilon_eq := by simp
  constant_eq := by simp
  determinant := by simp
  frame_bound := by simpa only [Finset.range_zero, Finset.sum_empty, mul_zero, Real.exp_zero] using
    norm_matrixAction_one_le n
  inverse_bound := by simpa only [inv_one, Finset.range_zero, Finset.sum_empty, mul_zero, Real.exp_zero] using
    norm_matrixAction_one_le n
  density_eq := by intro x; simp only [pow_zero, one_smul, matrixAction_one_apply]

lemma WeightedIterationState.uniform_frame_bound
    {d₀ : NormalizedWeightedMomentData n 1 1} {ρ Q β : ℝ} {j : ℕ}
    (s : WeightedIterationState d₀ ρ Q β j) (hQ : 0 ≤ Q) (hβ : 0 ≤ β) (hβone : β < 1)
    (hbudget : Real.exp (2 * Q * d₀.epsilon / (1 - β)) ≤ 2) :
    ‖matrixAction s.frame‖ ≤ 2 :=
  s.frame_bound.trans ((exp_geometric_partial_sum_le hQ d₀.epsilon_pos.le hβ hβone j).trans hbudget)

lemma WeightedIterationState.uniform_inverse_bound
    {d₀ : NormalizedWeightedMomentData n 1 1} {ρ Q β : ℝ} {j : ℕ}
    (s : WeightedIterationState d₀ ρ Q β j) (hQ : 0 ≤ Q) (hβ : 0 ≤ β) (hβone : β < 1)
    (hbudget : Real.exp (2 * Q * d₀.epsilon / (1 - β)) ≤ 2) :
    ‖matrixAction s.frame⁻¹‖ ≤ 2 := by
  have hp : 0 ≤ Q * d₀.epsilon * ∑ k ∈ Finset.range j, β ^ k :=
    mul_nonneg (mul_nonneg hQ d₀.epsilon_pos.le) (Finset.sum_nonneg (fun k _ => pow_nonneg hβ k))
  have he : Real.exp (Q * d₀.epsilon * ∑ k ∈ Finset.range j, β ^ k) ≤
      Real.exp (2 * Q * d₀.epsilon * ∑ k ∈ Finset.range j, β ^ k) :=
    Real.exp_le_exp.mpr (by linarith)
  exact s.inverse_bound.trans (he.trans
    ((exp_geometric_partial_sum_le hQ d₀.epsilon_pos.le hβ hβone j).trans hbudget))

lemma WeightedIterationState.epsilon_le
    {d₀ : NormalizedWeightedMomentData n 1 1} {ρ Q β : ℝ} {j : ℕ}
    (s : WeightedIterationState d₀ ρ Q β j) (hβ : 0 ≤ β) (hβone : β ≤ 1) :
    s.data.epsilon ≤ d₀.epsilon := by
  rw [s.epsilon_eq]
  exact mul_le_of_le_one_right d₀.epsilon_pos.le (pow_le_one₀ hβ hβone)

lemma WeightedIterationState.next_density_bound
    {d₀ : NormalizedWeightedMomentData n 1 1} {ρ Q β α : ℝ} {j : ℕ}
    (s : WeightedIterationState d₀ ρ Q β j) (hQ : 0 ≤ Q) (hβ : 0 ≤ β) (hβone : β < 1)
    (hbudget : Real.exp (2 * Q * d₀.epsilon / (1 - β)) ≤ 2)
    (hα : 0 < α) (hρ : 0 < ρ) (hρsmall : 2 * ρ < 1)
    (hcompatible : (2 * ρ) ^ α ≤ β ^ 2)
    (hholder : ∀ x ∈ closedBall (0 : Space n) 1,
      |weightedDataDensity d₀ x - 1| ≤ d₀.epsilon ^ 2 * ‖x‖ ^ α) :
    ∀ x ∈ closedBall (0 : Space n) ρ,
      |weightedDataDensity s.data x - 1| ≤ (β * s.data.epsilon) ^ 2 := by
  intro x hx
  rw [s.density_eq, s.epsilon_eq]
  exact density_bound_at_iterated_point hα hρ hρsmall hcompatible hholder
    (s.uniform_frame_bound hQ hβ hβone hbudget) j hx

end KLS
end

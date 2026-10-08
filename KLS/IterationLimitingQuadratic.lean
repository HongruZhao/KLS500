import KLS.QuadraticCoefficientBounds

open Matrix Set Filter Metric InnerProductSpace
open scoped Topology BigOperators Matrix.Norms.Elementwise
noncomputable section
namespace KLS
variable {n : ℕ}

lemma weighted_geometric_tail_le
    {C r β : ℝ} (hC : 0 ≤ C) (hr : 0 ≤ r) (hrone : r ≤ 1)
    (hβ : 0 ≤ β) (hβone : β < 1) (j : ℕ) :
    C * (r * β) ^ j / (1 - r * β) ≤ C / (1 - β) * β ^ j * r ^ j := by
  have hd : 1 - β ≤ 1 - r * β := by nlinarith
  have hh := div_le_div_of_nonneg_left (mul_nonneg hC (pow_nonneg (mul_nonneg hr hβ) j))
    (sub_pos.mpr hβone) hd
  apply hh.trans_eq
  rw [mul_pow]
  ring

/-- A proved weighted flatness iteration determines one positive definite,
determinant-one limiting quadratic, and the original function approaches that
quadratic uniformly on the actual shrinking Euclidean balls. -/
theorem iteration_limiting_quadratic_approximation
    {d₀ : NormalizedWeightedMomentData n 1 1} {ρ Q β : ℝ}
    (s : (j : ℕ) → WeightedIterationState d₀ ρ Q β j)
    (hlinks : ∀ j, Nonempty (WeightedIterationLink (s j) (s (j + 1))))
    (hstart : s 0 = initialWeightedIterationState d₀ ρ Q β)
    (hinv : ∀ j, ‖matrixAction (s j).frame⁻¹‖ ≤ 2)
    (hρ : 0 < ρ) (hρsmall : ρ / 2 ≤ 1) (hQ : 0 ≤ Q) (hβ : 0 ≤ β) (hβone : β < 1) :
    ∃ (H : Matrix (Fin n) (Fin n) ℝ) (p : Space n) (a : ℝ),
      H.PosDef ∧ H.det = 1 ∧
      ∀ (j : ℕ) (x : Space n), ‖x‖ ≤ (ρ / 2) ^ j / 2 →
        |d₀.u x - centeredQuadratic H 0 p a x| ≤
          (1 + 5 * (Q / (1 - β))) * d₀.epsilon * β ^ j * (ρ / 2) ^ (2 * j) := by
  let links : ∀ j, WeightedIterationLink (s j) (s (j + 1)) := fun j => Classical.choice (hlinks j)
  obtain ⟨H, hHpos, hHdet, _, hHtail⟩ := weighted_iteration_hessian_limit s hlinks hinv hβone
  obtain ⟨p, a, _, _, hptail, hatail⟩ :=
    iteration_affine_coefficients_limits s links hinv hρ.le hρsmall hβ hβone
  refine ⟨H, p, a, hHpos, hHdet, ?_⟩
  intro j x hx
  have hr : 0 ≤ ρ / 2 := by positivity
  have ht : 0 ≤ (ρ / 2) ^ j := pow_nonneg hr j
  have he : 0 ≤ d₀.epsilon * β ^ j := mul_nonneg d₀.epsilon_pos.le (pow_nonneg hβ j)
  have hK : 0 ≤ Q / (1 - β) := div_nonneg hQ (sub_pos.mpr hβone).le
  have hs : (ρ / 2) ^ 2 ≤ 1 := by nlinarith
  have hp : ‖iterationSlope s links j - p‖ ≤
      2 * (Q / (1 - β)) * (d₀.epsilon * β ^ j) * (ρ / 2) ^ j := by
    have hh := (hptail j).trans (weighted_geometric_tail_le
      (mul_nonneg (mul_nonneg (by norm_num) hQ) d₀.epsilon_pos.le) hr hρsmall hβ hβone j)
    exact hh.trans_eq (by ring)
  have ha : |iterationConstant s links j - a| ≤
      (Q / (1 - β)) * (d₀.epsilon * β ^ j) * ((ρ / 2) ^ j) ^ 2 := by
    have hh := (hatail j).trans (weighted_geometric_tail_le
      (mul_nonneg hQ d₀.epsilon_pos.le) (sq_nonneg (ρ / 2)) hs hβ hβone j)
    apply hh.trans_eq
    rw [← pow_mul, Nat.mul_comm 2 j, pow_mul]
    ring
  have hH : ‖matrixAction (frameHessian (s j).frame - H)‖ ≤
      4 * (Q / (1 - β)) * (d₀.epsilon * β ^ j) := (hHtail j).trans_eq (by ring)
  have hu := iteration_quadratic_error_on_ball s links hstart hρ hinv j hx
  have hpowers : (ρ / 2) ^ (2 * j) = ((ρ / 2) ^ j) ^ 2 := by rw [← pow_mul, Nat.mul_comm]
  rw [hpowers] at hu ⊢
  have hb := quadratic_error_of_coefficient_bounds he ht hK
    (hx.trans (by linarith : (ρ / 2) ^ j / 2 ≤ (ρ / 2) ^ j)) hu hH hp ha
  exact hb.trans_eq (by ring)

/-- The complete perturbative conclusion from the original normalized
weighted moment datum and its small Holder density error. No iteration or
quadratic-limit oracle is a hypothesis. -/
theorem weighted_exists_limiting_quadratic (hn : 0 < n) {α : ℝ} (hα : 0 < α) :
    ∃ ρ β C Δ : ℝ, 0 < ρ ∧ ρ ≤ 1 / 512 ∧ 1 / 2 ≤ β ∧ β < 1 ∧
      0 < C ∧ 0 < Δ ∧
      ∀ d₀ : NormalizedWeightedMomentData n 1 1, d₀.epsilon < Δ →
      (∀ x ∈ closedBall (0 : Space n) 1,
        |weightedDataDensity d₀ x - 1| ≤ d₀.epsilon ^ 2 * ‖x‖ ^ α) →
      ∃ (H : Matrix (Fin n) (Fin n) ℝ) (p : Space n) (a : ℝ),
        H.PosDef ∧ H.det = 1 ∧
        ∀ (j : ℕ) (x : Space n), ‖x‖ ≤ (ρ / 2) ^ j / 2 →
          |d₀.u x - centeredQuadratic H 0 p a x| ≤ C * d₀.epsilon * β ^ j * (ρ / 2) ^ (2 * j) := by
  obtain ⟨ρ, Q, β, Δ, hρ, hρsmall, hQ, hβhalf, hβone, _, hΔ, hiter⟩ :=
    exists_weighted_flatness_iteration hn hα
  let C := 1 + 5 * (Q / (1 - β))
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨ρ, β, C, Δ, hρ, hρsmall, hβhalf, hβone, hC, hΔ, ?_⟩
  intro d₀ hd hholder
  obtain ⟨s, hstart, hlinks, hframes⟩ := hiter d₀ hd hholder
  exact iteration_limiting_quadratic_approximation s hlinks hstart (fun j => (hframes j).2)
    hρ (by linarith) hQ.le (by linarith) hβone

end KLS
end

import KLS.WeightedIterationSuccessor

open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff NNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

/-- Actual infinite improvement iteration from one normalized starting
quadratic and a Holder density bound. Every state is a genuine weighted
potential, every link is the actual rescale-and-whiten operation, and the
original density supplies every tighter density bound. There is no assumed
iteration, compactness principle, or regularity conclusion in the inputs. -/
theorem exists_weighted_flatness_iteration (hn : 0 < n) {α : ℝ} (hα : 0 < α) :
    ∃ ρ Q β Δ : ℝ, 0 < ρ ∧ ρ ≤ 1 / 512 ∧ 0 < Q ∧
      1 / 2 ≤ β ∧ β < 1 ∧ (2 * ρ) ^ α ≤ β ^ 2 ∧ 0 < Δ ∧
      ∀ d₀ : NormalizedWeightedMomentData n 1 1, d₀.epsilon < Δ →
      (∀ x ∈ closedBall (0 : Space n) 1,
        |weightedDataDensity d₀ x - 1| ≤ d₀.epsilon ^ 2 * ‖x‖ ^ α) →
      ∃ s : (j : ℕ) → WeightedIterationState d₀ ρ Q β j,
        s 0 = initialWeightedIterationState d₀ ρ Q β ∧
        (∀ j, Nonempty (WeightedIterationLink (s j) (s (j + 1)))) ∧
        (∀ j, ‖matrixAction (s j).frame‖ ≤ 2 ∧ ‖matrixAction ((s j).frame⁻¹)‖ ≤ 2) := by
  obtain ⟨ρ, δ, Q, hρ, hρbound, hδ, hQ, hstep⟩ := weighted_improvement_successor hn
  have hρsmall : 2 * ρ < 1 := by linarith
  obtain ⟨β, hβ, hβone, hβhalf, hcompatible⟩ :=
    exists_compatible_density_flatness_rate (show 0 < 2 * ρ by positivity) hρsmall hα
      (θ := 1 / 2) (by norm_num) (by norm_num)
  let Δ := min δ (min ((1 / 2) / Q) (Real.log 2 * (1 - β) / (2 * Q)))
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hΔ : 0 < Δ := lt_min hδ (lt_min (by positivity) (by positivity))
  refine ⟨ρ, Q, β, Δ, hρ, hρbound, hQ, hβhalf, hβone, hcompatible, hΔ, ?_⟩
  intro d₀ hd hholder
  have hsmall : d₀.epsilon < δ := hd.trans_le (min_le_left _ _)
  have hhalf : Q * d₀.epsilon ≤ 1 / 2 := by
    have hh := (le_div_iff₀ hQ).mp (hd.le.trans
      ((min_le_right _ _).trans (min_le_left _ _)))
    linarith
  have hbudget : Real.exp (2 * Q * d₀.epsilon / (1 - β)) ≤ 2 := by
    have hh := (le_div_iff₀ (show 0 < 2 * Q by positivity)).mp
      (hd.le.trans ((min_le_right _ _).trans (min_le_right _ _)))
    have he : 2 * Q * d₀.epsilon / (1 - β) ≤ Real.log 2 := by
      apply (div_le_iff₀ (sub_pos.mpr hβone)).mpr
      linarith
    exact (Real.exp_le_exp.mpr he).trans_eq (Real.exp_log (by norm_num))
  have hnext (j : ℕ) (s : WeightedIterationState d₀ ρ Q β j) :
      ∃ t : WeightedIterationState d₀ ρ Q β (j + 1), Nonempty (WeightedIterationLink s t) :=
    s.exists_successor hstep hρ hρsmall hQ.le hβhalf hβone hα hcompatible hsmall hhalf hbudget hholder
  let next (j : ℕ) (s : WeightedIterationState d₀ ρ Q β j) :
      WeightedIterationState d₀ ρ Q β (j + 1) := Classical.choose (hnext j s)
  let states : (j : ℕ) → WeightedIterationState d₀ ρ Q β j :=
    Nat.rec (initialWeightedIterationState d₀ ρ Q β) (fun j s => next j s)
  refine ⟨states, rfl, ?_, ?_⟩
  · intro j
    exact Classical.choose_spec (hnext j (states j))
  · intro j
    exact ⟨(states j).uniform_frame_bound hQ.le hβ.le hβone hbudget,
      (states j).uniform_inverse_bound hQ.le hβ.le hβone hbudget⟩

end KLS
end

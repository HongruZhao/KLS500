import KLS.WeightedImprovementSuccessor
import KLS.GeometricDensityFlatness

open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff NNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

lemma geometric_partial_sum_le {β : ℝ} (hβ : 0 ≤ β) (hβone : β < 1) (j : ℕ) :
    (∑ k ∈ Finset.range j, β ^ k) ≤ 1 / (1 - β) := by
  simpa only [Nat.Ico_zero_eq_range, pow_zero] using
    geom_sum_Ico_le_of_lt_one (m := 0) (n := j) hβ hβone

lemma exp_geometric_partial_sum_le {Q ε β : ℝ} (hQ : 0 ≤ Q) (hε : 0 ≤ ε)
    (hβ : 0 ≤ β) (hβone : β < 1) (j : ℕ) :
    Real.exp (2 * Q * ε * ∑ k ∈ Finset.range j, β ^ k) ≤
      Real.exp (2 * Q * ε / (1 - β)) := by
  apply Real.exp_le_exp.mpr
  simpa only [mul_one_div] using mul_le_mul_of_nonneg_left
    (geometric_partial_sum_le hβ hβone j) (by positivity : 0 ≤ 2 * Q * ε)

/-- Uniform frame control and the literal scalar radius put the entire
next comparison ball inside a compatible geometric physical radius. -/
lemma norm_iterated_physical_point_le
    {T : Matrix (Fin n) (Fin n) ℝ} (hT : ‖matrixAction T‖ ≤ 2)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (j : ℕ) {x : Space n} (hx : x ∈ closedBall (0 : Space n) ρ) :
    ‖(ρ / 2) ^ j • matrixAction T x‖ ≤ (2 * ρ) ^ (j + 1) := by
  have hxn : ‖x‖ ≤ ρ := by simpa only [mem_closedBall, dist_zero_right] using hx
  have hpow : (ρ / 2) ^ j ≤ (2 * ρ) ^ j := pow_le_pow_left₀ (by positivity) (by linarith) j
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (by positivity) j)]
  calc
    _ ≤ (ρ / 2) ^ j * (‖matrixAction T‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left ((matrixAction T).le_opNorm x) (pow_nonneg (by positivity) j)
    _ ≤ (2 * ρ) ^ j * (2 * ρ) :=
      mul_le_mul hpow (mul_le_mul hT hxn (norm_nonneg _) (by norm_num))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (pow_nonneg (by positivity) j)
    _ = _ := (pow_succ _ _).symm

/-- The proved spatial estimate closes the sharper density hypothesis for
one successive weighted improvement. All density values belong to the
original function at actual physical points. -/
theorem density_bound_at_iterated_point
    {f : Space n → ℝ} {ε β α ρ : ℝ} (hα : 0 < α)
    (hρ : 0 < ρ) (hρsmall : 2 * ρ < 1)
    (hcompatible : (2 * ρ) ^ α ≤ β ^ 2)
    (hholder : ∀ x ∈ closedBall (0 : Space n) 1,
      |f x - 1| ≤ ε ^ 2 * ‖x‖ ^ α)
    {T : Matrix (Fin n) (Fin n) ℝ} (hT : ‖matrixAction T‖ ≤ 2)
    (j : ℕ) {x : Space n} (hx : x ∈ closedBall (0 : Space n) ρ) :
    |f ((ρ / 2) ^ j • matrixAction T x) - 1| ≤ (β * (ε * β ^ j)) ^ 2 := by
  let y := (ρ / 2) ^ j • matrixAction T x
  have hn : ‖y‖ ≤ (2 * ρ) ^ (j + 1) := norm_iterated_physical_point_le hT hρ.le j hx
  have hy : y ∈ closedBall (0 : Space n) 1 := by
    rw [mem_closedBall, dist_zero_right]
    exact hn.trans (pow_le_one₀ (by positivity) hρsmall.le)
  have hp := Real.rpow_le_rpow (norm_nonneg y) hn hα.le
  have hc : ((2 * ρ) ^ α) ^ (j + 1) ≤ (β ^ 2) ^ (j + 1) :=
    pow_le_pow_left₀ (Real.rpow_nonneg (by positivity) _) hcompatible _
  calc
    _ ≤ ε ^ 2 * ‖y‖ ^ α := hholder y hy
    _ ≤ ε ^ 2 * (((2 * ρ) ^ (j + 1) : ℝ) ^ α) := mul_le_mul_of_nonneg_left hp (sq_nonneg ε)
    _ = ε ^ 2 * ((2 * ρ) ^ α) ^ (j + 1) := by rw [Real.rpow_pow_comm (by positivity : 0 ≤ 2 * ρ)]
    _ ≤ ε ^ 2 * (β ^ 2) ^ (j + 1) := mul_le_mul_of_nonneg_left hc (sq_nonneg ε)
    _ = _ := by rw [← pow_mul, Nat.mul_comm 2 (j + 1), pow_mul, pow_succ, mul_pow]; ring

end KLS
end

import KLS.WeightedResolventSquarePairBound

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology ContDiff ENNReal RealInnerProductSpace

noncomputable section
namespace KLS

/-- The square root along a geometric partition has its exact ratio. -/
theorem sqrt_geometric_time {t q : ℝ} (ht : 0 ≤ t) (hq : 0 ≤ q) (k : ℕ) :
    Real.sqrt (t * (q ^ 2) ^ k) = Real.sqrt t * q ^ k := by
  rw [Real.sqrt_mul ht]
  congr 1
  rw [← pow_mul, Nat.mul_comm 2 k, pow_mul, Real.sqrt_sq (pow_nonneg hq k)]

/-- Retaining the exact partition ratio avoids the previous dyadic widening. -/
theorem resolvent_ratio_step_coefficient {a q B : ℝ} (ha : 0 < a) (hq : 0 < q) :
    (a - q ^ 2 * a) *
        (B / Real.sqrt (2 * a) + B / Real.sqrt (2 * (q ^ 2 * a))) =
      (1-q) * ((q+2+q⁻¹) / Real.sqrt 2) * B * Real.sqrt a := by
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hs2 : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  rw [show 2 * (q ^ 2 * a) = q ^ 2 * (2*a) by ring,
    Real.sqrt_mul (sq_nonneg q), Real.sqrt_sq hq.le,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  field_simp [ne_of_gt hs, ne_of_gt hs2, ne_of_gt hq]
  linear_combination -(B * (q+1-q^2-q^3)) * (Real.sq_sqrt ha.le)

/-- Exact geometric step weights telescope without widening their ratio. -/
theorem abs_limit_sub_zero_le_of_geometric_steps {F : ℕ → ℝ} {L C q : ℝ}
    (hC : 0 ≤ C) (hq : 0 ≤ q) (hlim : Tendsto F atTop (𝓝 L))
    (hstep : ∀ k, |F (k + 1) - F k| ≤ C * (1-q) * q ^ k) :
    |L-F 0| ≤ C := by
  have hb (k : ℕ) : |F k-F 0| ≤ C*(1-q^k) := by
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        _ = |(F (k+1)-F k)+(F k-F 0)| := by congr 1; ring
        _ ≤ |F (k+1)-F k|+|F k-F 0| := abs_add_le _ _
        _ ≤ C*(1-q)*q^k+C*(1-q^k) := add_le_add (hstep k) ih
        _ = _ := by rw [pow_succ]; ring
  apply le_of_tendsto' ((hlim.sub_const (F 0)).abs)
  intro k
  exact (hb k).trans (by nlinarith [pow_nonneg hq k])

end KLS
end

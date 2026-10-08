import KLS.IterationLimitingQuadratic

open Matrix Set Filter Metric InnerProductSpace Asymptotics
open scoped Topology BigOperators Matrix.Norms.Elementwise
noncomputable section
namespace KLS
variable {n : ℕ}

lemma geometric_remainder_zero
    {f : Space n → ℝ} {D r β : ℝ} (hD : 0 ≤ D)
    (hr : 0 < r) (hrone : r < 1) (hβ : 0 ≤ β) (hβone : β < 1)
    (hb : ∀ (j : ℕ) (x : Space n), ‖x‖ ≤ r ^ j / 2 →
      |f x| ≤ D * β ^ j * r ^ (2 * j)) : f 0 = 0 := by
  have hbound (j : ℕ) : |f 0| ≤ D * β ^ j := by
    have hh := hb j 0 (by simpa only [norm_zero] using div_nonneg (pow_nonneg hr.le j) (by norm_num))
    exact hh.trans (mul_le_of_le_one_right (mul_nonneg hD (pow_nonneg hβ j))
      (pow_le_one₀ hr.le hrone.le))
  have hlim : Tendsto (fun j : ℕ => D * β ^ j) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one hβ hβone)
  have hz : |f 0| ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds hlim (Eventually.of_forall hbound)
  exact abs_eq_zero.mp (le_antisymm hz (abs_nonneg _))

/-- Geometric ball estimates with a decaying flatness factor yield a
second-order remainder on every sufficiently small displacement. -/
theorem geometric_second_order_remainder
    {f : Space n → ℝ} {D r β : ℝ} (hD : 0 ≤ D)
    (hr : 0 < r) (hrone : r < 1) (hβ : 0 ≤ β) (hβone : β < 1)
    (hb : ∀ (j : ℕ) (x : Space n), ‖x‖ ≤ r ^ j / 2 →
      |f x| ≤ D * β ^ j * r ^ (2 * j)) :
    ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ x : Space n, ‖x‖ < δ → |f x| ≤ η * ‖x‖ ^ 2 := by
  intro η hη
  have hden : 0 < 4 * (D + 1) := by positivity
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one
    (show 0 < η * r ^ 2 / (4 * (D + 1)) by positivity) hβone
  have hrate : 4 * D * β ^ N ≤ η * r ^ 2 := by
    have hh := (lt_div_iff₀ hden).mp hN
    nlinarith [pow_nonneg hβ N]
  refine ⟨r ^ N / 2, by positivity, ?_⟩
  intro x hx
  by_cases hxzero : x = 0
  · rw [hxzero, geometric_remainder_zero hD hr hrone hβ hβone hb, abs_zero, norm_zero]
    norm_num
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hxzero
  have hxone : 2 * ‖x‖ ≤ 1 := by
    have hh : r ^ N ≤ 1 := pow_le_one₀ hr.le hrone.le
    linarith
  obtain ⟨j, hjlow, hjhigh⟩ := exists_nat_pow_near_of_lt_one
    (show 0 < 2 * ‖x‖ by positivity) hxone hr hrone
  have hjN : N ≤ j := by
    by_contra! h
    have hh := pow_le_pow_of_le_one hr.le hrone.le (show j + 1 ≤ N by omega)
    linarith
  have hβpow : β ^ j ≤ β ^ N := pow_le_pow_of_le_one hβ hβone.le hjN
  have hscale : r ^ j ≤ (2 / r) * ‖x‖ := by
    have hh : r ^ j * r ≤ 2 * ‖x‖ := by simpa only [pow_succ] using hjlow.le
    have := (le_div_iff₀ hr).mpr hh
    exact this.trans_eq (by ring)
  have hscale2 : (r ^ j) ^ 2 ≤ (2 / r) ^ 2 * ‖x‖ ^ 2 := by
    have hnon := pow_nonneg hr.le j
    nlinarith
  have hcoef : D * β ^ N * (2 / r) ^ 2 ≤ η := by
    calc
      _ = 4 * D * β ^ N / r ^ 2 := by ring
      _ ≤ η := (div_le_iff₀ (sq_pos_of_pos hr)).mpr hrate
  have hh := hb j x (by linarith)
  have hp : r ^ (2 * j) = (r ^ j) ^ 2 := by rw [← pow_mul, Nat.mul_comm]
  rw [hp] at hh
  calc
    |f x| ≤ D * β ^ j * (r ^ j) ^ 2 := hh
    _ ≤ D * β ^ N * ((2 / r) ^ 2 * ‖x‖ ^ 2) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hβpow hD) hscale2 (sq_nonneg _) (mul_nonneg hD (pow_nonneg hβ N))
    _ = (D * β ^ N * (2 / r) ^ 2) * ‖x‖ ^ 2 := by ring
    _ ≤ η * ‖x‖ ^ 2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)

theorem geometric_remainder_isLittleO
    {f : Space n → ℝ} {D r β : ℝ} (hD : 0 ≤ D)
    (hr : 0 < r) (hrone : r < 1) (hβ : 0 ≤ β) (hβone : β < 1)
    (hb : ∀ (j : ℕ) (x : Space n), ‖x‖ ≤ r ^ j / 2 →
      |f x| ≤ D * β ^ j * r ^ (2 * j)) :
    f =o[𝓝 (0 : Space n)] (fun x => ‖x‖ ^ 2) := by
  apply Asymptotics.IsLittleO.of_bound
  intro η hη
  obtain ⟨δ, hδ, hsmall⟩ := geometric_second_order_remainder hD hr hrone hβ hβone hb η hη
  filter_upwards [Metric.ball_mem_nhds (0 : Space n) hδ] with x hx
  have hx' : ‖x‖ < δ := by simpa only [mem_ball_zero_iff] using hx
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖x‖)] using hsmall x hx'

end KLS
end

import KLS.MomentDyadicGradientModulus
import Mathlib.Topology.MetricSpace.Holder

/-! Geometric decay at dyadic distances yields a genuine real-power Hölder
bound. The positive exponent is constructed from the proved decay factor. -/

open MeasureTheory InnerProductSpace Set Filter Metric
open scoped Topology NNReal ENNReal

noncomputable section
namespace KLS

theorem exists_holder_exponent_of_geometric_decay {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧ q ≤ (1 / 2 : ℝ) ^ α := by
  let α₀ : ℝ := Real.log q / Real.log (1 / 2 : ℝ)
  have hhalf : Real.log (1 / 2 : ℝ) < 0 := Real.log_neg (by norm_num) (by norm_num)
  have hα₀ : 0 < α₀ := div_pos_of_neg_of_neg (Real.log_neg hq hq1) hhalf
  have heq : (1 / 2 : ℝ) ^ α₀ = q := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have hmul : Real.log (1 / 2 : ℝ) * α₀ = Real.log q := by
      dsimp [α₀]
      field_simp
    rw [hmul, Real.exp_log hq]
  refine ⟨min 1 α₀, lt_min zero_lt_one hα₀, min_le_left _ _, ?_⟩
  rw [← heq]
  exact Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (min_le_right _ _)

theorem exists_holder_bound_of_dyadic_modulus
    {n m : ℕ} {g : Space n → Space m} {c : Space n} {r q M : ℝ}
    (hr : 0 < r) (hq : 0 < q) (hq1 : q < 1) (hM : 0 ≤ M)
    (hdyadic : ∀ x ∈ closedBall c r, ∀ k : ℕ, ∀ y : Space n,
      ‖y - x‖ ≤ r * (1 / 2 : ℝ) ^ (k + 1) → ‖g y - g x‖ ≤ M * q ^ k) :
    ∃ α A : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 < A ∧
      ∀ x ∈ closedBall c (r / 4), ∀ y ∈ closedBall c (r / 4),
        ‖g y - g x‖ ≤ A * ‖y - x‖ ^ α := by
  obtain ⟨α, hα, hα1, hqα⟩ := exists_holder_exponent_of_geometric_decay hq hq1
  let A : ℝ := 1 + M * (4 / r) ^ α
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨α, A, hα, hα1, hA, ?_⟩
  intro x hx y hy
  by_cases hxy : y = x
  · subst y
    simp only [sub_self, norm_zero]
    positivity
  have hd : 0 < ‖y - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hdsize : ‖y - x‖ ≤ r / 2 := by
    have hxn : ‖x - c‖ ≤ r / 4 := hx
    have hyn : ‖y - c‖ ≤ r / 4 := hy
    have htri := norm_sub_le_norm_sub_add_norm_sub y c x
    rw [norm_sub_rev c x] at htri
    linarith
  have hparam : 0 < 2 * ‖y - x‖ / r := by positivity
  have hparam1 : 2 * ‖y - x‖ / r ≤ 1 := (div_le_one hr).mpr (by linarith)
  obtain ⟨k, hlow, hupp⟩ := exists_nat_pow_near_of_lt_one hparam hparam1
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  have hdscale : ‖y - x‖ ≤ r * (1 / 2 : ℝ) ^ (k + 1) := by
    have hh := (div_le_iff₀ hr).mp hupp
    rw [pow_succ]
    nlinarith
  have hxouter : x ∈ closedBall c r :=
    closedBall_subset_closedBall (by linarith : r / 4 ≤ r) hx
  have hbound := hdyadic x hxouter k y hdscale
  have hpowdist : (1 / 2 : ℝ) ^ k ≤ 4 * ‖y - x‖ / r := by
    rw [pow_succ] at hlow
    calc
      _ ≤ 2 * (2 * ‖y - x‖ / r) := by linarith
      _ = _ := by ring
  have hpowbound : q ^ k ≤ (4 / r) ^ α * ‖y - x‖ ^ α := by
    calc
      _ ≤ ((1 / 2 : ℝ) ^ α) ^ k := pow_le_pow_left₀ hq.le hqα k
      _ = ((1 / 2 : ℝ) ^ k) ^ α := Real.rpow_pow_comm (by norm_num) α k
      _ ≤ (4 * ‖y - x‖ / r) ^ α := Real.rpow_le_rpow (by positivity) hpowdist hα.le
      _ = (4 / r) ^ α * ‖y - x‖ ^ α := by
        rw [show 4 * ‖y - x‖ / r = (4 / r) * ‖y - x‖ by ring,
          Real.mul_rpow (by positivity : 0 ≤ 4 / r) hd.le]
  have hscaled := mul_le_mul_of_nonneg_left hpowbound hM
  have hnonneg : 0 ≤ ‖y - x‖ ^ α := Real.rpow_nonneg (norm_nonneg _) _
  dsimp [A]
  nlinarith

theorem exists_local_moment_gradient_holder_bound
    {n : ℕ} (hn : 0 < n) {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : Continuous V)
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    (c : Space n) :
    ∃ r α A : ℝ, 0 < r ∧ 0 < α ∧ α ≤ 1 ∧ 0 < A ∧
      ∀ x ∈ closedBall c r, ∀ y ∈ closedBall c r,
        ‖gradient u y - gradient u x‖ ≤ A * ‖y - x‖ ^ α := by
  obtain ⟨r, q, hr, hq, hq1, hmod⟩ :=
    exists_local_moment_gradient_dyadic_modulus hn hLip hc hV hK hKc hpush c
  obtain ⟨α, A, hα, hα1, hA, hholder⟩ :=
    exists_holder_bound_of_dyadic_modulus hr hq hq1 (by positivity : 0 ≤ 4 * (L : ℝ)) hmod
  exact ⟨r / 4, α, A, by positivity, hα, hα1, hA, hholder⟩

end KLS
end

#print axioms KLS.exists_holder_exponent_of_geometric_decay
#print axioms KLS.exists_holder_bound_of_dyadic_modulus
#print axioms KLS.exists_local_moment_gradient_holder_bound

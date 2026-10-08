import KLS.RadialAverageDerivative
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff NNReal BigOperators
noncomputable section
set_option maxHeartbeats 800000
namespace KLS
variable {n : ℕ}

/-- The genuine Lebesgue change of variables writes each radial average on
a fixed unit ball, with the dimension factor canceled exactly. -/
lemma integral_radialAverageKernel_eq_rescaled (u : Space n → ℝ) (a : ℝ → ℝ)
    (c : Space n) {t : ℝ} (ht : 0 < t) :
    (∫ x, u x * radialAverageKernel a c t x) =
      ∫ y, u (c + t • y) * a (‖y‖ ^ 2) := by
  let G : Space n → ℝ := fun y => u (c + t • y) * a (‖y‖ ^ 2)
  have he := integral_add_right_eq_self (μ := volume) (fun x => u x * radialAverageKernel a c t x) c
  rw [← he]
  have hfun : (fun x => u (x+c) * radialAverageKernel a c t (x+c)) =
      fun y => G (t⁻¹ • y) / t ^ n := by
    funext y
    dsimp only [G, radialAverageKernel, radialSquaredCoordinate]
    rw [add_sub_cancel_right, smul_smul, mul_inv_cancel₀ ht.ne', one_smul,
      norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht, mul_pow, inv_pow]
    rw [add_comm c y]
    rw [show ‖y‖ ^ 2 / t ^ 2 = t⁻¹ ^ 2 * ‖y‖ ^ 2 by rw [div_eq_mul_inv, inv_pow, mul_comm]]
    rw [mul_div_assoc, inv_pow]
  rw [hfun]
  simp_rw [div_eq_mul_inv]
  rw [integral_mul_const, Measure.integral_comp_inv_smul_of_nonneg volume G ht.le]
  simp only [Space, finrank_euclideanSpace_fin, smul_eq_mul]
  dsimp only [G]
  rw [mul_assoc, mul_comm (∫ y : Space n, u (c + t • y) * a (‖y‖ ^ 2)) ((t ^ n)⁻¹),
    ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero n ht.ne'), one_mul]

/-- Fixed-support domination proves the shrinking radial average limit at
every continuity point; global integrability of u is unnecessary. -/
theorem tendsto_rescaled_radialAverage {u : Space n → ℝ} (hu : Continuous u)
    {a : ℝ → ℝ} (ha : ContDiff ℝ 1 a) (ha0 : ∀ s, 1 ≤ s → a s = 0)
    (c : Space n) :
    Tendsto (fun t : ℝ => ∫ y, u (c + t • y) * a (‖y‖ ^ 2)) (𝓝 0)
      (𝓝 (u c * ∫ y : Space n, a (‖y‖ ^ 2))) := by
  let κ : Space n → ℝ := fun y => a (‖y‖ ^ 2)
  have hκ : Continuous κ := by
    have he : κ = radialAverageKernel a (0 : Space n) 1 := by
      funext y
      simp [κ, radialAverageKernel, radialSquaredCoordinate]
    rw [he]
    exact (contDiff_radialAverageKernel ha 0 1).continuous
  have hκs : tsupport κ ⊆ closedBall (0 : Space n) 1 := by
    have he : κ = radialAverageKernel a (0 : Space n) 1 := by
      funext y
      simp [κ, radialAverageKernel, radialSquaredCoordinate]
    rw [he]
    exact tsupport_radialAverageKernel_subset_closedBall ha0 0 zero_lt_one
  have hκc : HasCompactSupport κ :=
    (isCompact_closedBall (0 : Space n) 1).of_isClosed_subset (isClosed_tsupport _) hκs
  have hκi : Integrable κ volume := hκ.integrable_of_hasCompactSupport hκc
  obtain ⟨B, hB⟩ := (isCompact_closedBall c 1).exists_bound_of_continuousOn hu.continuousOn
  have hh : ContinuousAt (fun t : ℝ => ∫ y, u (c + t • y) * κ y) 0 := by
    apply continuousAt_of_dominated (μ := volume)
      (F := fun t y => u (c + t • y) * κ y) (bound := fun y => B * ‖κ y‖)
    · exact Eventually.of_forall fun t =>
        (show Continuous (fun y : Space n => u (c + t • y) * κ y) by fun_prop).aestronglyMeasurable
    · filter_upwards [ball_mem_nhds (0 : ℝ) zero_lt_one] with t ht
      apply Eventually.of_forall
      intro y
      by_cases hy : y ∈ tsupport κ
      · have hy1 : ‖y‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hκs hy
        have ht1 : |t| < 1 := by simpa only [mem_ball, Real.dist_eq, sub_zero] using ht
        have hcy : c + t • y ∈ closedBall c 1 := by
          rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
          exact (mul_le_mul ht1.le hy1 (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hB _ hcy) (norm_nonneg _)
      · rw [image_eq_zero_of_notMem_tsupport hy, mul_zero, norm_zero, mul_zero]
    · exact hκi.norm.const_mul B
    · exact Eventually.of_forall fun y =>
        (((hu.comp (continuous_const.add (continuous_id.smul continuous_const))).mul continuous_const).continuousAt)
  simpa only [ContinuousAt, zero_smul, add_zero, integral_const_mul, κ] using hh

/-- The actual compact radial averages converge from positive scales to
the center value times their fixed mass. -/
theorem tendsto_radialAverage {u : Space n → ℝ} (hu : Continuous u)
    {a : ℝ → ℝ} (ha : ContDiff ℝ 1 a) (ha0 : ∀ s, 1 ≤ s → a s = 0)
    (c : Space n) :
    Tendsto (fun t => ∫ x, u x * radialAverageKernel a c t x) (𝓝[>] 0)
      (𝓝 (u c * ∫ y : Space n, a (‖y‖ ^ 2))) := by
  apply ((tendsto_rescaled_radialAverage hu ha ha0 c).mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (integral_radialAverageKernel_eq_rescaled u a c ht).symm

/-- An arbitrary-dimensional local weighted mean-value inequality for
actual continuous distribution subharmonic functions. -/
theorem subharmonic_le_radialAverage {u : Space n → ℝ} (hu : Continuous u)
    {a : ℝ → ℝ} (ha : ContDiff ℝ 1 a) (ha0 : ∀ s, 1 ≤ s → a s = 0)
    (han : ∀ s, 0 ≤ a s) {c : Space n} {t R : ℝ} (ht : 0 < t) (htR : t < R)
    (hdist : ∀ ψ : Space n → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ ball c R → (∀ x, 0 ≤ ψ x) →
      0 ≤ ∫ x, u x * coordinateLaplacian ψ x) :
    u c * (∫ y : Space n, a (‖y‖ ^ 2)) ≤ ∫ x, u x * radialAverageKernel a c t x := by
  have hm := monotoneOn_radialAverage_of_distribution hu ha ha0 han hdist
  apply le_of_tendsto (tendsto_radialAverage hu ha ha0 c)
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ht)] with s hs hst
  exact hm ⟨hs, lt_trans hst htR⟩ ⟨ht, htR⟩ hst.le

end KLS
end

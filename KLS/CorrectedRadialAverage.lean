import KLS.RadialKernelUniformBounds

open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff NNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

/-- A quadratic correction contributes at most epsilon times the squared
outer radius to the genuine normalized radial mean-value inequality. -/
theorem upper_average_of_subharmonic_quadratic_correction
    {w : Space n → ℝ} (hw : Continuous w) {ε t R s : ℝ} (hε : 0 ≤ ε)
    (ht : 0 < t) (htR : t < R) (hs : 0 ≤ s) {c : Space n}
    (hκs : tsupport (radialAverageKernel (normalizedRadialProfile n) c t) ⊆ closedBall (0 : Space n) s)
    (hdist : ∀ ψ : Space n → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ ball c R → (∀ x, 0 ≤ ψ x) →
      0 ≤ ∫ x, (w x + ε * ‖x‖ ^ 2) * coordinateLaplacian ψ x) :
    w c ≤ (∫ x, w x * radialAverageKernel (normalizedRadialProfile n) c t x) + ε * s ^ 2 := by
  let κ := radialAverageKernel (normalizedRadialProfile n) c t
  have hκ := continuous_normalizedRadialKernel c t
  have hκc := hasCompactSupport_normalizedRadialKernel c ht
  have hκ0 (x : Space n) : 0 ≤ κ x :=
    radialAverageKernel_nonneg (normalizedRadialProfile_nonneg n) c x ht
  have hκi : Integrable κ volume := hκ.integrable_of_hasCompactSupport hκc
  have hn2 : Continuous (fun x : Space n => ‖x‖ ^ 2) := continuous_id.norm.pow 2
  have hwi : Integrable (fun x => w x * κ x) :=
    (hw.mul hκ).integrable_of_hasCompactSupport hκc.mul_left
  have hni : Integrable (fun x : Space n => ‖x‖ ^ 2 * κ x) :=
    (hn2.mul hκ).integrable_of_hasCompactSupport hκc.mul_left
  have hbound : (∫ x : Space n, ‖x‖ ^ 2 * κ x) ≤ s ^ 2 := by
    have hh : (∫ x : Space n, ‖x‖ ^ 2 * κ x) ≤ ∫ x, s ^ 2 * κ x := by
      apply integral_mono hni (hκi.const_mul (s ^ 2))
      intro x
      dsimp only
      by_cases hx : x ∈ tsupport κ
      · have hn : ‖x‖ ≤ s := by simpa only [mem_closedBall, dist_zero_right] using hκs hx
        exact mul_le_mul_of_nonneg_right (by nlinarith [norm_nonneg x] : ‖x‖ ^ 2 ≤ s ^ 2) (hκ0 x)
      · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero, mul_zero]
    simpa only [integral_const_mul, integral_normalizedRadialKernel c ht, mul_one, κ] using hh
  have hm := subharmonic_le_normalizedRadialAverage (hw.add (continuous_const.mul hn2)) ht htR hdist
  have heq : (∫ x, (w x + ε * ‖x‖ ^ 2) * κ x) =
      (∫ x, w x * κ x) + ε * (∫ x : Space n, ‖x‖ ^ 2 * κ x) := by
    have hp : (fun x => (w x + ε * ‖x‖ ^ 2) * κ x) =
        (fun x => w x * κ x + ε * (‖x‖ ^ 2 * κ x)) := by funext x; ring
    rw [hp, integral_add hwi (hni.const_mul ε), integral_const_mul]
  change w c + ε * ‖c‖ ^ 2 ≤ ∫ x, (w x + ε * ‖x‖ ^ 2) * κ x at hm
  rw [heq] at hm
  have hh := mul_le_mul_of_nonneg_left hbound hε
  have hpos := mul_nonneg hε (sq_nonneg ‖c‖)
  linarith

lemma lower_average_of_subharmonic_negative_quadratic_correction
    {v : Space n → ℝ} (hv : Continuous v) {ε t R s : ℝ} (hε : 0 ≤ ε)
    (ht : 0 < t) (htR : t < R) (hs : 0 ≤ s) {c : Space n}
    (hκs : tsupport (radialAverageKernel (normalizedRadialProfile n) c t) ⊆ closedBall (0 : Space n) s)
    (hdist : ∀ ψ : Space n → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ ball c R → (∀ x, 0 ≤ ψ x) →
      0 ≤ ∫ x, (-v x + ε * ‖x‖ ^ 2) * coordinateLaplacian ψ x) :
    (∫ x, v x * radialAverageKernel (normalizedRadialProfile n) c t x) - ε * s ^ 2 ≤ v c := by
  have hh := upper_average_of_subharmonic_quadratic_correction hv.neg hε ht htR hs hκs hdist
  change -v c ≤ (∫ x, -v x * radialAverageKernel (normalizedRadialProfile n) c t x) + ε * s ^ 2 at hh
  simp_rw [neg_mul, integral_neg] at hh
  linarith

end KLS
end

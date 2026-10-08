import KLS.RadialKernelCalculus
import KLS.CompactParameterIntegral

open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff NNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

lemma continuous_radialAverageKernelScaleDerivative {a : ℝ → ℝ} (ha : ContDiff ℝ 1 a)
    (c : Space n) (t : ℝ) : Continuous (radialAverageKernelScaleDerivative a c t) := by
  have hq := (contDiff_radialSquaredCoordinate c t).continuous
  have hda := ha.continuous_deriv (by norm_num)
  exact (((continuous_const.mul (ha.continuous.comp hq)).add
    ((continuous_const.mul hq).mul (hda.comp hq))).neg).div_const _

lemma continuousOn_radialAverageKernelScaleDerivative {a : ℝ → ℝ} (ha : ContDiff ℝ 1 a)
    (c : Space n) {S : Set (ℝ × Space n)} (hS : ∀ p ∈ S, p.1 ≠ 0) :
    ContinuousOn (fun p => radialAverageKernelScaleDerivative a c p.1 p.2) S := by
  have hq : ContinuousOn (fun p : ℝ × Space n => radialSquaredCoordinate c p.1 p.2) S :=
    (((continuous_snd.sub continuous_const).norm.pow 2).continuousOn).div
      ((continuous_fst.pow 2).continuousOn) (fun p hp => pow_ne_zero _ (hS p hp))
  have hda := ha.continuous_deriv (by norm_num)
  exact (((continuousOn_const.mul (ha.continuous.comp_continuousOn hq)).add
    ((continuousOn_const.mul hq).mul (hda.comp_continuousOn hq))).neg).div
      ((continuous_fst.pow (n+1)).continuousOn) (fun p hp => pow_ne_zero _ (hS p hp))

lemma support_radialAverageKernelScaleDerivative_subset_closedBall {a : ℝ → ℝ}
    (ha : ContDiff ℝ 1 a) (ha0 : ∀ s, 1 ≤ s → a s = 0)
    (c : Space n) {t : ℝ} (ht : 0 < t) :
    Function.support (radialAverageKernelScaleDerivative a c t) ⊆ closedBall c t := by
  intro x hx
  by_contra hnot
  have htail := tsupport_radialTailTest_subset_closedBall ha0 c ht
  have hL : coordinateLaplacian (fun y => radialTailProfile a (radialSquaredCoordinate c t y)) x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hh => hnot (htail (tsupport_coordinateLaplacian_subset _ hh)))
  exact hx (by rw [radialAverageKernelScaleDerivative_eq_laplacian ha c x ht.ne', hL, mul_zero])

/-- The actual radial average is differentiable in scale, justified by a
fixed compact support on a neighborhood of each positive scale. -/
theorem hasDerivAt_radialAverage {u : Space n → ℝ} (hu : Continuous u)
    {a : ℝ → ℝ} (ha : ContDiff ℝ 1 a) (ha0 : ∀ s, 1 ≤ s → a s = 0)
    (c : Space n) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun r => ∫ x, u x * radialAverageKernel a c r x)
      (∫ x, u x * radialAverageKernelScaleDerivative a c t x) t := by
  apply hasDerivAt_integral_of_local_common_compact_support (r := t/2) (by positivity)
    (K := closedBall c (2*t)) (isCompact_closedBall _ _)
    (fun r => hu.mul (contDiff_radialAverageKernel ha c r).continuous)
    (fun r => hu.mul (continuous_radialAverageKernelScaleDerivative ha c r))
  · exact (hu.comp continuous_snd).continuousOn.mul
      (continuousOn_radialAverageKernelScaleDerivative ha c (fun p hp => by
        have hp0 := hp.1.1
        linarith))
  · intro s hs x hx
    have hs0 : 0 < s := by linarith [hs.1]
    exact (closedBall_subset_closedBall (by linarith [hs.2] : s ≤ 2*t))
      ((tsupport_radialAverageKernel_subset_closedBall ha0 c hs0)
        (tsupport_mul_subset_right (subset_closure hx)))
  · intro x hx
    apply closedBall_subset_closedBall (by linarith : t ≤ 2*t)
    apply support_radialAverageKernelScaleDerivative_subset_closedBall ha ha0 c ht
    exact right_ne_zero_of_mul hx
  · intro x s hs
    have hs0 : s ≠ 0 := ne_of_gt (by linarith [hs.1] : 0 < s)
    exact (hasDerivAt_radialAverageKernel ha c x hs0).const_mul (u x)

lemma radialAverage_deriv_nonneg_of_distribution {u : Space n → ℝ} (hu : Continuous u)
    {a : ℝ → ℝ} (ha : ContDiff ℝ 1 a) (ha0 : ∀ s, 1 ≤ s → a s = 0)
    (han : ∀ s, 0 ≤ a s) {c : Space n} {t R : ℝ} (ht : 0 < t) (htR : t < R)
    (hdist : ∀ ψ : Space n → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ ball c R → (∀ x, 0 ≤ ψ x) →
      0 ≤ ∫ x, u x * coordinateLaplacian ψ x) :
    0 ≤ deriv (fun r => ∫ x, u x * radialAverageKernel a c r x) t := by
  rw [(hasDerivAt_radialAverage hu ha ha0 c ht).deriv]
  let ψ : Space n → ℝ := fun x => radialTailProfile a (radialSquaredCoordinate c t x)
  have hψ := contDiff_radialTailTest ha c t
  have hs := tsupport_radialTailTest_subset_closedBall ha0 c ht
  have hψc : HasCompactSupport ψ :=
    (isCompact_closedBall c t).of_isClosed_subset (isClosed_tsupport _) hs
  have hnonneg := hdist ψ hψ hψc (hs.trans (closedBall_subset_ball htR))
    (fun _ => radialTailProfile_nonneg han ha0 _)
  have he : (fun x => u x * radialAverageKernelScaleDerivative a c t x) =
      (fun x => (t / (2 * t ^ n)) * (u x * coordinateLaplacian ψ x)) := by
    funext x
    rw [radialAverageKernelScaleDerivative_eq_laplacian ha c x ht.ne']
    dsimp only [ψ]
    ring
  rw [he, integral_const_mul]
  exact mul_nonneg (by positivity) hnonneg

/-- Local distribution subharmonicity makes every positive compact radial
average monotone in scale, in every finite dimension. -/
theorem monotoneOn_radialAverage_of_distribution {u : Space n → ℝ} (hu : Continuous u)
    {a : ℝ → ℝ} (ha : ContDiff ℝ 1 a) (ha0 : ∀ s, 1 ≤ s → a s = 0)
    (han : ∀ s, 0 ≤ a s) {c : Space n} {R : ℝ}
    (hdist : ∀ ψ : Space n → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ ball c R → (∀ x, 0 ≤ ψ x) →
      0 ≤ ∫ x, u x * coordinateLaplacian ψ x) :
    MonotoneOn (fun r => ∫ x, u x * radialAverageKernel a c r x) (Ioo 0 R) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioo _ _)
  · exact fun r hr => (hasDerivAt_radialAverage hu ha ha0 c hr.1).continuousAt.continuousWithinAt
  · intro r hr
    exact (hasDerivAt_radialAverage hu ha ha0 c (interior_subset hr).1).differentiableAt.differentiableWithinAt
  · intro r hr
    exact radialAverage_deriv_nonneg_of_distribution hu ha ha0 han (interior_subset hr).1
      (interior_subset hr).2 hdist

end KLS
end

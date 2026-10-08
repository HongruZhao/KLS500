import KLS.ViscosityHarmonicDistribution
import KLS.MollificationLocalization

open MeasureTheory InnerProductSpace Set Filter Metric ContinuousLinearMap
open scoped ContDiff ENNReal Convolution Topology
noncomputable section
namespace KLS
variable {n : ℕ}

lemma coordinateLaplacian_scalarConvolution {v κ : Space n → ℝ}
    (hv : LocallyIntegrable v volume) (hκ : ContDiff ℝ 2 κ)
    (hc : HasCompactSupport κ) (a : Space n) :
    coordinateLaplacian (scalarConvolution v κ) a =
      ∫ y, v y * coordinateLaplacian κ (a - y) := by
  have hi (i : Fin n) : Integrable (fun y => v y * coordinateHessian κ (a - y) i i) :=
    (hasCompactSupport_coordinateHessian hc i i).convolutionExists_right (lsmul ℝ ℝ)
      hv (contDiff_coordinateHessian hκ (m := 0) (by norm_num) i i).continuous a
  unfold coordinateLaplacian
  calc
    (∑ i, coordinateHessian (scalarConvolution v κ) a i i) =
        ∑ i, ∫ y, v y * coordinateHessian κ (a - y) i i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [coordinateHessian_scalarConvolution hv hκ hc]
      rfl
    _ = _ := by
      rw [← integral_finsetSum _ (fun i _ => hi i)]
      apply integral_congr_ae
      exact Eventually.of_forall fun y => by dsimp only; rw [Finset.mul_sum]

lemma coordinateLaplacian_const_sub {κ : Space n → ℝ} (hκ : ContDiff ℝ 2 κ)
    (a y : Space n) :
    coordinateLaplacian (fun z => κ (a - z)) y = coordinateLaplacian κ (a - y) := by
  unfold coordinateLaplacian
  exact Finset.sum_congr rfl (fun i _ => coordinateHessian_const_sub hκ a y i i)

lemma tsupport_reflected_mollifier_subset (k : ℕ) (a : Space n) :
    tsupport (fun y => mollifierKernel n k (a - y)) ⊆
      closedBall a (2 * cutoffScale k) := by
  apply (isClosed_closedBall).closure_subset_iff.mpr
  intro y hy
  have hmem : a - y ∈ ball (0 : Space n) (2 * cutoffScale k) := by
    have hm := Function.mem_support.mpr hy
    rw [mollifierKernel, (mollifierBump n k).support_normed_eq] at hm
    exact hm
  have hd : dist y a < 2 * cutoffScale k := by
    simpa only [mem_ball, dist_zero_right, dist_eq_norm, sub_zero, norm_sub_rev] using hmem
  exact hd.le

/-- A continuous or locally integrable distribution-harmonic function has
classically harmonic actual mollifications on each smaller ball once the kernel
is sufficiently small. Only nonnegative test functions are needed. -/
theorem eventually_laplacian_mollify_eq_zero_on_closedBall
    {v : Space n → ℝ} (hv : LocallyIntegrable v volume) {c : Space n} {r R : ℝ}
    (hrR : r < R)
    (hdist : ∀ φ : Space n → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
      tsupport φ ⊆ ball c R → (∀ x, 0 ≤ φ x) →
      (∫ x, v x * coordinateLaplacian φ x) = 0) :
    ∀ᶠ k : ℕ in atTop, ∀ a ∈ closedBall c r, coordinateLaplacian (mollify k v) a = 0 := by
  have ht : Tendsto (fun k => 2 * cutoffScale k) atTop (𝓝 0) := by
    simpa using cutoffScale_tendsto_zero.const_mul 2
  filter_upwards [ht.eventually (eventually_lt_nhds (sub_pos.mpr hrR))] with k hk a ha
  let φ : Space n → ℝ := fun y => mollifierKernel n k (a - y)
  have hκ : ContDiff ℝ 2 (mollifierKernel n k) := (mollifierKernel_contDiff k).of_le (by simp)
  have hφ : ContDiff ℝ 2 φ := hκ.comp (contDiff_const.sub contDiff_id)
  have hφc : HasCompactSupport φ :=
    (mollifierKernel_hasCompactSupport k).comp_homeomorph (Homeomorph.subLeft a)
  have hφs : tsupport φ ⊆ ball c R := by
    intro y hy
    have hy' := tsupport_reflected_mollifier_subset k a hy
    have htri := dist_triangle y a c
    have hya : dist y a ≤ 2 * cutoffScale k := hy'
    have hac : dist a c ≤ r := ha
    change dist y c < R
    linarith
  have he := hdist φ hφ hφc hφs (fun y => (mollifierBump n k).nonneg_normed (a - y))
  rw [mollify, coordinateLaplacian_scalarConvolution hv hκ (mollifierKernel_hasCompactSupport k)]
  convert he using 1
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    dsimp only
    rw [show coordinateLaplacian φ y = coordinateLaplacian (mollifierKernel n k) (a - y) from
      coordinateLaplacian_const_sub hκ a y]

end KLS
end

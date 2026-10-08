import KLS.WeightedCompactSmoothing
import KLS.HarmonicInteriorGradient

open MeasureTheory InnerProductSpace Set Filter Metric ContinuousLinearMap
open scoped Topology ContDiff ENNReal Convolution Pointwise
noncomputable section
namespace KLS
open EllipticPdes.Sobolev EllipticPdes.Regularity
variable {n : ℕ}

lemma mollify_nonneg {f : Space n → ℝ} (hf : ∀ x, 0 ≤ f x) (k : ℕ) (x : Space n) :
    0 ≤ mollify k f x := by
  unfold mollify scalarConvolution
  rw [convolution_def]
  apply integral_nonneg
  intro y
  exact mul_nonneg (hf y) ((mollifierBump n k).nonneg_normed (x-y))

lemma eventually_tsupport_mollify_subset_ball {f : Space n → ℝ}
    {c : Space n} {r R : ℝ} (hs : tsupport f ⊆ closedBall c r) (hrR : r < R) :
    ∀ᶠ k : ℕ in atTop, tsupport (mollify k f) ⊆ ball c R := by
  have ht : Tendsto (fun k => 2 * cutoffScale k) atTop (𝓝 0) := by
    simpa using cutoffScale_tendsto_zero.const_mul 2
  filter_upwards [ht.eventually (eventually_lt_nhds (sub_pos.mpr hrR))] with k hk
  have hclosed : tsupport (mollify k f) ⊆ closedBall c (r + 2 * cutoffScale k) := by
    apply (isClosed_closedBall).closure_subset_iff.mpr
    intro x hx
    have hmem := (support_convolution_subset (lsmul ℝ ℝ)) hx
    obtain ⟨y, hy, z, hz, rfl⟩ := hmem
    have hyc : dist y c ≤ r := hs (subset_tsupport f hy)
    have hzc : ‖z‖ < 2 * cutoffScale k := by
      rw [mollifierKernel, (mollifierBump n k).support_normed_eq] at hz
      simpa only [mem_ball, dist_zero_right, mollifierBump] using hz
    change dist (y+z) c ≤ r + 2 * cutoffScale k
    have htri : dist (y+z) c ≤ dist y c + ‖z‖ := by
      simpa only [add_sub_right_comm, dist_eq_norm] using norm_add_le (y-c) z
    linarith
  exact hclosed.trans (closedBall_subset_ball (by linarith))

/-- Compact C1 tests and their actual derivatives can be mollified inside
integral pairings with any continuous coefficient. -/
lemma tendsto_integral_mul_coordinateDerivative_mollify {φ b : Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (hb : Continuous b) (i : Fin n) :
    Tendsto (fun k => ∫ x, b x * coordinateDerivative (mollify k φ) i x) atTop
      (𝓝 (∫ x, b x * coordinateDerivative φ i x)) := by
  let K := mollifierEnlargement (tsupport φ)
  have hK : IsCompact K := isCompact_mollifierEnlargement hc
  obtain ⟨χ, hχ, hχ1, -⟩ := exists_isTestFn_one_nhdsSet_of_isCompact hK isOpen_univ (subset_univ K)
  have hχc : HasCompactSupport χ := hχ.2.1
  have hχcont : Continuous χ := hχ.1.continuous
  have hχeq : ∀ x ∈ K, χ x = 1 := fun x hx => hχ1.self_of_nhdsSet x hx
  have hφ2 : MemLp φ 2 volume := hφ.continuous.memLp_of_hasCompactSupport hc
  have hdφ : Continuous (coordinateDerivative φ i) :=
    (contDiff_coordinateDerivative hφ (m := 0) (by norm_num) i).continuous
  have hdφ2 : MemLp (coordinateDerivative φ i) 2 volume :=
    hdφ.memLp_of_hasCompactSupport (hasCompactSupport_coordinateDerivative hc i)
  have hφLip : LocallyLipschitz φ := hφ.locallyLipschitz
  have ht := tendsto_integral_mul_of_eLpNorm_sub_tendsto_zero
    (fun k => (contDiff_coordinateDerivative
      ((mollify_contDiff hφ.continuous.locallyIntegrable k).of_le (by simp) : ContDiff ℝ 1 (mollify k φ))
      (m := 0) (by norm_num) i).continuous.memLp_of_hasCompactSupport
        (hasCompactSupport_coordinateDerivative (hasCompactSupport_mollify hc k) i))
    hdφ2 ((hχcont.mul hb).memLp_of_hasCompactSupport hχc.mul_right)
    (eLpNorm_mollify_coordinateDerivative_sub_tendsto_zero hφLip hφ2 i hdφ2)
  have heq {g : Space n → ℝ} (hgs : tsupport g ⊆ K) :
      (∫ x, χ x * b x * g x) = ∫ x, b x * g x := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only
      by_cases hx : x ∈ tsupport g
      · rw [hχeq x (hgs hx), one_mul]
      · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero, mul_zero]
  have hlim : tsupport (coordinateDerivative φ i) ⊆ K :=
    (tsupport_coordinateDerivative_subset φ i).trans (subset_mollifierEnlargement _)
  have hk (k : ℕ) : tsupport (coordinateDerivative (mollify k φ) i) ⊆ K :=
    (tsupport_coordinateDerivative_subset _ i).trans (tsupport_mollify_subset hc k)
  simpa only [Pi.mul_apply, heq hlim, heq (hk _)] using ht

end KLS
end

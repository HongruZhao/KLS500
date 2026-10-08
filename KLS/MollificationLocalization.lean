import KLS.MollificationApproximation
import KLS.WeightedMollification

/-!
# Local control of the actual mollifications

Every kernel in the fixed sequence is supported in the radius-two ball.
On a compact set, mollification therefore agrees with mollification of an
actual compact restriction of the input. Global Young bounds and strong L²
approximation can consequently be applied without a global L² assumption.
-/

open MeasureTheory InnerProductSpace Set Filter ContinuousLinearMap
open scoped ContDiff ENNReal Convolution Topology Pointwise

noncomputable section
namespace KLS

variable {n : ℕ}

lemma cutoffScale_le_one (k : ℕ) : cutoffScale k ≤ 1 := by
  change ((k : ℝ) + 1)⁻¹ ≤ 1
  rw [← one_div, div_le_one (by positivity)]
  nlinarith [Nat.cast_nonneg (α := ℝ) k]

lemma mollifierKernel_support_subset (k : ℕ) :
    Function.support (mollifierKernel n k) ⊆ Metric.closedBall 0 2 := by
  rw [mollifierKernel, (mollifierBump n k).support_normed_eq]
  apply Metric.ball_subset_closedBall.trans
  apply Metric.closedBall_subset_closedBall
  change 2 * cutoffScale k ≤ 2
  nlinarith [cutoffScale_le_one k]

/-- The compact enlargement containing every input point used by our kernels. -/
def mollifierEnlargement (K : Set (Space n)) : Set (Space n) :=
  K + Metric.closedBall 0 2

lemma isCompact_mollifierEnlargement {K : Set (Space n)} (hK : IsCompact K) :
    IsCompact (mollifierEnlargement K) := hK.add (isCompact_closedBall _ _)

/-- On K, actual mollification only sees the actual radius-two enlargement of K. -/
theorem mollify_eq_indicator_on {f : Space n → ℝ} {K : Set (Space n)} (k : ℕ)
    {x : Space n} (hx : x ∈ K) :
    mollify k f x = mollify k ((mollifierEnlargement K).indicator f) x := by
  unfold mollify scalarConvolution
  rw [convolution_def, convolution_def]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro y
  by_cases hκ : mollifierKernel n k (x - y) = 0
  · simp [hκ]
  · have hxy := mollifierKernel_support_subset (n := n) k (Function.mem_support.mpr hκ)
    have hyx : y - x ∈ Metric.closedBall (0 : Space n) 2 := by
      simpa only [Metric.mem_closedBall, dist_zero_right, norm_sub_rev] using hxy
    have hy : y ∈ mollifierEnlargement K := by
      have he := Set.add_mem_add hx hyx
      simpa only [mollifierEnlargement, add_sub_cancel] using he
    simp [Set.indicator_of_mem hy]

/-- Global L² membership of the exact compact restriction used in localization. -/
theorem memLp_mollifier_restriction {f : Space n → ℝ} {K : Set (Space n)} (hK : IsCompact K)
    (hf : ∀ S : Set (Space n), IsCompact S → MemLp f 2 (volume.restrict S)) :
    MemLp ((mollifierEnlargement K).indicator f) 2 volume :=
  (memLp_indicator_iff_restrict (isCompact_mollifierEnlargement hK).measurableSet.nullMeasurableSet).mpr
    (hf _ (isCompact_mollifierEnlargement hK))

/-- L² membership of every mollification of a globally L² input. -/
theorem memLp_mollify {f : Space n → ℝ} (hf : MemLp f 2 volume) (k : ℕ) :
    MemLp (mollify k f) 2 volume := (eLpNorm_mollify_le hf k).trans_lt hf

lemma integral_sq_eq_toReal_eLpNorm_sq {μ : Measure (Space n)} {f : Space n → ℝ}
    (hf : MemLp f 2 μ) : (∫ x, f x ^ 2 ∂μ) = (eLpNorm f 2 μ).toReal ^ 2 := by
  let v : Lp ℝ 2 μ := hf.toLp f
  have he : (∫ x, f x ^ 2 ∂μ) = inner ℝ v v := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with x hx
    simp [v, hx, pow_two]
  rw [he, real_inner_self_eq_norm_sq]
  change ‖hf.toLp f‖ ^ 2 = _
  rw [Lp.norm_toLp]

theorem integral_sq_mollify_le {f : Space n → ℝ} (hf : MemLp f 2 volume) (k : ℕ) :
    (∫ x, mollify k f x ^ 2) ≤ ∫ x, f x ^ 2 := by
  rw [integral_sq_eq_toReal_eLpNorm_sq (memLp_mollify hf k),
    integral_sq_eq_toReal_eLpNorm_sq hf]
  exact pow_le_pow_left₀ ENNReal.toReal_nonneg
    (ENNReal.toReal_mono hf.eLpNorm_ne_top (eLpNorm_mollify_le hf k)) 2

/-- A global L² bound for a continuous compact multiplier. -/
theorem memLp_compact_mul_of_local {χ f : Space n → ℝ} (hχ : Continuous χ)
    (hc : HasCompactSupport χ)
    (hf : ∀ K : Set (Space n), IsCompact K → MemLp f 2 (volume.restrict K)) :
    MemLp (fun x => χ x * f x) 2 volume := by
  have hfi : MemLp ((tsupport χ).indicator f) 2 volume :=
    (memLp_indicator_iff_restrict hc.measurableSet.nullMeasurableSet).mpr (hf _ hc)
  have hm : MemLp (χ * (tsupport χ).indicator f) 2 volume :=
    (hχ.memLp_top_of_hasCompactSupport hc volume).mul hfi
  convert hm using 1
  funext x
  by_cases hx : x ∈ tsupport χ
  · simp [hx]
  · simp [hx, image_eq_zero_of_notMem_tsupport hx]

/-- The actual compactly localized approximants retain the local input and converge in L². -/
theorem eLpNorm_compact_mul_mollify_sub_tendsto_zero {χ f : Space n → ℝ}
    (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hf : ∀ K : Set (Space n), IsCompact K → MemLp f 2 (volume.restrict K)) :
    Tendsto (fun k => eLpNorm (fun x => χ x * mollify k f x - χ x * f x) 2 volume)
      atTop (𝓝 0) := by
  let fK := (mollifierEnlargement (tsupport χ)).indicator f
  have hfK : MemLp fK 2 volume := memLp_mollifier_restriction hc hf
  have heq (k : ℕ) : (fun x => χ x * mollify k f x - χ x * f x) =
      χ * (mollify k fK - fK) := by
    funext x
    by_cases hx : x ∈ tsupport χ
    · have hxK : x ∈ mollifierEnlargement (tsupport χ) := by
        have hz : (0 : Space n) ∈ Metric.closedBall 0 2 := by simp
        simpa only [mollifierEnlargement, add_zero] using Set.add_mem_add hx hz
      rw [mollify_eq_indicator_on k hx]
      simp [fK, hxK, mul_sub]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  simp_rw [heq]
  have hbound (k : ℕ) : eLpNorm (χ * (mollify k fK - fK)) 2 volume ≤
      eLpNorm χ ⊤ volume * eLpNorm (mollify k fK - fK) 2 volume := by
    exact eLpNorm_smul_le_mul_eLpNorm
      (hχ.memLp_top_of_hasCompactSupport hc volume).aestronglyMeasurable
      ((memLp_mollify hfK k).sub hfK).aestronglyMeasurable
  have htop := (hχ.memLp_top_of_hasCompactSupport hc volume).eLpNorm_ne_top
  have ht : Tendsto (fun k => eLpNorm χ ⊤ volume * eLpNorm (mollify k fK - fK) 2 volume)
      atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul (eLpNorm_mollify_sub_tendsto_zero hfK) (Or.inr htop)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => bot_le) hbound


/-- A fixed compact multiplier gives a uniform ordinary L² bound for locally L² inputs. -/
theorem exists_uniform_integral_sq_compact_mul_mollify {χ f : Space n → ℝ}
    (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hf : ∀ K : Set (Space n), IsCompact K → MemLp f 2 (volume.restrict K)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k : ℕ, (∫ x, χ x ^ 2 * mollify k f x ^ 2) ≤ M := by
  let fK := (mollifierEnlargement (tsupport χ)).indicator f
  have hfK : MemLp fK 2 volume := memLp_mollifier_restriction hc hf
  have hfloc := locallyIntegrable_of_memLp_two_on_compacts hf
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hχ
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  refine ⟨C ^ 2 * (∫ x, fK x ^ 2), mul_nonneg (sq_nonneg _)
    (integral_nonneg (fun _ => sq_nonneg _)), ?_⟩
  intro k
  have hleft : Integrable (fun x => χ x ^ 2 * mollify k f x ^ 2) volume :=
    ((hχ.pow 2).mul ((mollify_contDiff hfloc k).continuous.pow 2)).integrable_of_hasCompactSupport
      (by simpa [pow_two, Pi.mul_def] using hc.mul_right.mul_right)
  have hright := ((memLp_mollify hfK k).integrable_sq).const_mul (C ^ 2)
  have hpoint (x : Space n) : χ x ^ 2 * mollify k f x ^ 2 ≤ C ^ 2 * mollify k fK x ^ 2 := by
    by_cases hx : x ∈ tsupport χ
    · rw [mollify_eq_indicator_on k hx]
      have hsq : χ x ^ 2 ≤ C ^ 2 := by
        simpa only [Real.norm_eq_abs, sq_abs] using pow_le_pow_left₀ (norm_nonneg _) (hC x) 2
      exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    · simp only [image_eq_zero_of_notMem_tsupport hx, zero_pow two_ne_zero, zero_mul]
      positivity
  have he := integral_mono hleft hright hpoint
  rw [integral_const_mul] at he
  exact he.trans (mul_le_mul_of_nonneg_left (integral_sq_mollify_le hfK k) (sq_nonneg _))

end KLS
end

#print axioms KLS.mollify_eq_indicator_on
#print axioms KLS.integral_sq_mollify_le
#print axioms KLS.memLp_compact_mul_of_local
#print axioms KLS.eLpNorm_compact_mul_mollify_sub_tendsto_zero

#print axioms KLS.exists_uniform_integral_sq_compact_mul_mollify

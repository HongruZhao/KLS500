import KLS.WeightedFaithfulSmoothing
import KLS.WeightedCompactL2Maps
import KLS.WeightedWeakEquation

/-! Strong weighted Sobolev approximation of compact locally Lipschitz functions by actual mollifiers. -/

open MeasureTheory InnerProductSpace Set Filter Metric
open scoped Topology ContDiff ENNReal Pointwise

noncomputable section
namespace KLS
variable {n : ℕ}

/-- A compactly supported weighted L² function is unweighted L² for a continuous positive weight. -/
theorem memLp_volume_of_potentialMeasure_hasCompactSupport {φ f : Space n → ℝ}
    (hf : MemLp f 2 (potentialMeasure φ)) (hφ : Continuous φ) (hc : HasCompactSupport f) :
    MemLp f 2 volume := by
  have hi := KLS.MemLp.restrict_volume_of_potentialMeasure hf hφ hc
  have h := (memLp_indicator_iff_restrict hc.measurableSet.nullMeasurableSet).mpr hi
  have he : (tsupport f).indicator f = f := by
    funext x
    by_cases hx : x ∈ tsupport f
    · simp only [indicator_of_mem hx]
    · simp only [indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx]
  rwa [he] at h

/-- Fixed compact supports let actual unweighted L² convergence pass to the weighted L² space. -/
theorem eLpNorm_potentialMeasure_sub_tendsto_zero_of_compact_support
    {φ : Space n → ℝ} (hφ : Continuous φ) {K : Set (Space n)} (hK : IsCompact K)
    {f : ℕ → Space n → ℝ} {g : Space n → ℝ}
    (hfK : ∀ k, tsupport (f k) ⊆ K) (hgK : tsupport g ⊆ K)
    (hfV : ∀ k, MemLp (f k) 2 volume) (hgV : MemLp g 2 volume)
    (hfμ : ∀ k, MemLp (f k) 2 (potentialMeasure φ)) (hgμ : MemLp g 2 (potentialMeasure φ))
    (hconv : Tendsto (fun k => eLpNorm (f k - g) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm (f k - g) 2 (potentialMeasure φ)) atTop (𝓝 0) := by
  obtain ⟨R, hR, hRK⟩ := hK.isBounded.subset_ball_lt 0 (0 : Space n)
  let χ : ContDiffBump (0 : Space n) := ⟨R, R + 1, hR, by linarith⟩
  have hχ (x : Space n) (hx : x ∈ K) : χ x = 1 :=
    χ.one_of_mem_closedBall (ball_subset_closedBall (hRK hx))
  let T := volumeL2CompactToWeighted hφ χ.continuous χ.hasCompactSupport
  have hT {v : Space n → ℝ} (hvK : tsupport v ⊆ K)
      (hvV : MemLp v 2 volume) (hvμ : MemLp v 2 (potentialMeasure φ)) :
      T (hvV.toLp v) = hvμ.toLp v := by
    apply Lp.ext
    filter_upwards [volumeL2CompactToWeighted_coe hφ χ.continuous χ.hasCompactSupport (hvV.toLp v),
      (withDensity_absolutelyContinuous _ _).ae_eq hvV.coeFn_toLp, hvμ.coeFn_toLp] with x hx hy hz
    rw [hx, hy, hz]
    by_cases hxs : x ∈ tsupport v
    · rw [hχ x (hvK hxs), one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hxs, mul_zero]
  have ht := T.continuous.tendsto (hgV.toLp g) |>.comp
    ((Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hfV g hgV).mpr hconv)
  have htw : Tendsto (fun k => (hfμ k).toLp (f k)) atTop (𝓝 (hgμ.toLp g)) := by
    simpa only [Function.comp_def, hT (hgK) hgV hgμ, hT (hfK _) (hfV _) (hfμ _)] using ht
  exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hfμ g hgμ).mp htw

lemma subset_mollifierEnlargement (K : Set (Space n)) : K ⊆ mollifierEnlargement K := by
  intro x hx
  have h := add_mem_add hx (show (0 : Space n) ∈ closedBall 0 2 by simp)
  simpa only [mollifierEnlargement, add_zero] using h

/-- The fixed explicit mollification sequence is a compact smooth weighted Sobolev approximation.
Only the actual weighted L² function and derivative hypotheses are required. -/
theorem compact_locallyLipschitz_weighted_smoothing
    {φ f : Space n → ℝ} (hφ : Continuous φ) (hf : LocallyLipschitz f)
    (hc : HasCompactSupport f) (hfμ : MemLp f 2 (potentialMeasure φ))
    (hdμ : ∀ i : Fin n, MemLp (coordinateDerivative f i) 2 (potentialMeasure φ)) :
    (∀ k, ContDiff ℝ 3 (mollify k f) ∧ HasCompactSupport (mollify k f) ∧
      MemLp (mollify k f) 2 (potentialMeasure φ) ∧
      ∀ i : Fin n, MemLp (coordinateDerivative (mollify k f) i) 2 (potentialMeasure φ)) ∧
    Tendsto (fun k => eLpNorm (mollify k f - f) 2 (potentialMeasure φ)) atTop (𝓝 0) ∧
    ∀ i : Fin n, Tendsto (fun k => eLpNorm
      (coordinateDerivative (mollify k f) i - coordinateDerivative f i) 2 (potentialMeasure φ))
      atTop (𝓝 0) := by
  have hfV := memLp_volume_of_potentialMeasure_hasCompactSupport hfμ hφ hc
  have hdV (i : Fin n) := memLp_volume_of_potentialMeasure_hasCompactSupport (hdμ i) hφ
    (hasCompactSupport_coordinateDerivative hc i)
  have hmk (k : ℕ) : ContDiff ℝ 3 (mollify k f) :=
    (mollify_contDiff (hfV.locallyIntegrable (by norm_num)) k).of_le (by simp)
  have hmc (k : ℕ) := hasCompactSupport_mollify hc k
  have hmμ (k : ℕ) := memLp_of_continuous_hasCompactSupport hφ (hmk k).continuous (hmc k)
  have hmdμ (k : ℕ) (i : Fin n) := memLp_of_continuous_hasCompactSupport hφ
    (contDiff_coordinateDerivative (hmk k) (m := 0) (by norm_num) i).continuous
    (hasCompactSupport_coordinateDerivative (hmc k) i)
  refine ⟨fun k => ⟨hmk k, hmc k, hmμ k, hmdμ k⟩, ?_, ?_⟩
  · exact eLpNorm_potentialMeasure_sub_tendsto_zero_of_compact_support hφ
      (isCompact_mollifierEnlargement hc) (tsupport_mollify_subset hc)
      (subset_mollifierEnlargement _) (fun k => memLp_mollify hfV k) hfV hmμ hfμ
      (eLpNorm_mollify_sub_tendsto_zero hfV)
  · intro i
    apply eLpNorm_potentialMeasure_sub_tendsto_zero_of_compact_support hφ
      (isCompact_mollifierEnlargement hc)
      (fun k => (tsupport_coordinateDerivative_subset _ i).trans (tsupport_mollify_subset hc k))
      ((tsupport_coordinateDerivative_subset _ i).trans (subset_mollifierEnlargement _))
      (fun k => (contDiff_coordinateDerivative (hmk k) (m := 0) (by norm_num) i).continuous.memLp_of_hasCompactSupport
        (hasCompactSupport_coordinateDerivative (hmc k) i))
      (hdV i) (fun k => hmdμ k i) (hdμ i)
    exact eLpNorm_mollify_coordinateDerivative_sub_tendsto_zero hf hfV i (hdV i)

end KLS
end

#print axioms KLS.eLpNorm_potentialMeasure_sub_tendsto_zero_of_compact_support
#print axioms KLS.compact_locallyLipschitz_weighted_smoothing

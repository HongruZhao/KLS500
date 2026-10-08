import KLS.WeakMomentInverseDivergence

open MeasureTheory Set Filter Matrix
open scoped Topology ContDiff NNReal ENNReal Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- Continuous multiplication preserves actual local L2 control. -/
theorem memLp_continuous_mul_on_compact
    {b c : Space n → ℝ} {S : Set (Space n)} (hS : IsCompact S)
    (hb : MemLp b 2 (volume.restrict S)) (hc : Continuous c) :
    MemLp (fun x => c x*b x) 2 (volume.restrict S) := by
  obtain ⟨C,hC⟩ := hS.bddAbove_image hc.norm.continuousOn
  apply hb.of_le_mul (c := C) (hc.aestronglyMeasurable.mul hb.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem hS.measurableSet] with x hx
  change ‖c x*b x‖ ≤ C*‖b x‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hC (mem_image_of_mem _ hx)) (norm_nonneg _)

/-- Actual local L2 coefficients pair integrably with compact continuous tests. -/
theorem integrable_mul_continuous_compact_of_localL2
    {φ b : Space n → ℝ} (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (hb : ∀ K : Set (Space n), IsCompact K → MemLp b 2 (volume.restrict K)) :
    Integrable (fun x => b x*φ x) := by
  have hb2 : MemLp ((tsupport φ).indicator b) 2 volume :=
    (memLp_indicator_iff_restrict hc.measurableSet.nullMeasurableSet).mpr (hb _ hc)
  have hint := hb2.integrable_mul (hφ.memLp_of_hasCompactSupport hc (p := 2) (μ := volume))
  apply hint.congr
  exact Eventually.of_forall fun x => by
    change (tsupport φ).indicator b x * φ x = _
    by_cases hx : x ∈ tsupport φ
    · rw [indicator_of_mem hx]
    · simp [image_eq_zero_of_notMem_tsupport hx]

/-- Mollified compact tests converge in their pairings with every locally
 L2 coefficient. -/
theorem tendsto_integral_mul_mollify_of_localL2
    {φ b : Space n → ℝ} (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (hb : ∀ K : Set (Space n), IsCompact K → MemLp b 2 (volume.restrict K)) :
    Tendsto (fun k => ∫ x, b x*mollify k φ x) atTop (𝓝 (∫ x, b x*φ x)) := by
  let K := mollifierEnlargement (tsupport φ)
  have hK : IsCompact K := isCompact_mollifierEnlargement hc
  have hφ2 : MemLp φ 2 volume := hφ.memLp_of_hasCompactSupport hc
  have hb2 : MemLp (K.indicator b) 2 volume :=
    (memLp_indicator_iff_restrict hK.measurableSet.nullMeasurableSet).mpr (hb K hK)
  have ht := tendsto_integral_mul_of_eLpNorm_sub_tendsto_zero
    (fun k => memLp_mollify hφ2 k) hφ2 hb2 (eLpNorm_mollify_sub_tendsto_zero hφ2)
  have heq {g : Space n → ℝ} (hgs : tsupport g ⊆ K) :
      (∫ x, K.indicator b x*g x) = ∫ x, b x*g x := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only
      by_cases hx : x ∈ K
      · rw [indicator_of_mem hx]
      · have hgx : g x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hgs h))
        rw [hgx,mul_zero,mul_zero]
  simpa only [heq (subset_mollifierEnlargement (tsupport φ)),heq (tsupport_mollify_subset hc _)] using ht

/-- A genuine locally L2 weak divergence equation extends to all compact
 locally Lipschitz tests, including its actual nonzero drift. -/
theorem integral_divergence_of_locallyLipschitz_test
    {A : Fin n → Space n → ℝ} {b : Space n → ℝ}
    (hA : ∀ i, ∀ K : Set (Space n), IsCompact K → MemLp (A i) 2 (volume.restrict K))
    (hb : ∀ K : Set (Space n), IsCompact K → MemLp b 2 (volume.restrict K))
    (hdiv : ∀ φ : Space n → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      (∑ i, ∫ x, A i x*coordinateDerivative φ i x) = ∫ x, b x*φ x)
    {φ : Space n → ℝ} (hφ : LocallyLipschitz φ) (hc : HasCompactSupport φ) :
    (∑ i, ∫ x, A i x*coordinateDerivative φ i x) = ∫ x, b x*φ x := by
  have hl := tendsto_finsetSum Finset.univ (fun i _ =>
    tendsto_integral_mul_coordinateDerivative_mollify_of_localL2 hφ hc (hA i) i)
  have hr := tendsto_integral_mul_mollify_of_localL2 hφ.continuous hc hb
  have he : (fun k => ∑ i, ∫ x, A i x*coordinateDerivative (mollify k φ) i x) =
      fun k => ∫ x, b x*mollify k φ x := by
    funext k
    exact hdiv _ ((mollify_contDiff hφ.continuous.locallyIntegrable k).of_le (by simp))
      (hasCompactSupport_mollify hc k)
  rw [he] at hl
  exact tendsto_nhds_unique hl hr

end KLS
end

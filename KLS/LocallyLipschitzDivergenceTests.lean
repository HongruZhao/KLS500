import KLS.WeakMomentHessianMollification
import KLS.MollifiedCompactTests

open MeasureTheory Set Filter Matrix
open scoped Topology ContDiff NNReal ENNReal Matrix.Norms.Elementwise
noncomputable section
namespace KLS
variable {n : ℕ}

/-- Local L2 control is sufficient for pairing a coefficient with the actual
 derivative of a compact locally Lipschitz test. -/
theorem integrable_mul_coordinateDerivative_of_localL2
    {φ b : Space n → ℝ} (hφ : LocallyLipschitz φ) (hc : HasCompactSupport φ)
    (hb : ∀ K : Set (Space n), IsCompact K → MemLp b 2 (volume.restrict K)) (i : Fin n) :
    Integrable (fun x => b x*coordinateDerivative φ i x) := by
  have hb2 : MemLp ((tsupport φ).indicator b) 2 volume :=
    (memLp_indicator_iff_restrict hc.measurableSet.nullMeasurableSet).mpr (hb _ hc)
  have hint := hb2.integrable_mul (memLp_volume_compact_coordinateDerivative hφ hc i)
  apply hint.congr
  exact Eventually.of_forall fun x => by
    change (tsupport φ).indicator b x * coordinateDerivative φ i x = _
    by_cases hx : x ∈ tsupport φ
    · rw [indicator_of_mem hx]
    · have hd : coordinateDerivative φ i x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hx (tsupport_coordinateDerivative_subset φ i h))
      simp [hd]

/-- Derivatives of actual compact locally Lipschitz tests converge in integral
 pairings with any actual locally L2 coefficient. -/
theorem tendsto_integral_mul_coordinateDerivative_mollify_of_localL2
    {φ b : Space n → ℝ} (hφ : LocallyLipschitz φ) (hc : HasCompactSupport φ)
    (hb : ∀ K : Set (Space n), IsCompact K → MemLp b 2 (volume.restrict K)) (i : Fin n) :
    Tendsto (fun k => ∫ x, b x*coordinateDerivative (mollify k φ) i x) atTop
      (𝓝 (∫ x, b x*coordinateDerivative φ i x)) := by
  let K := mollifierEnlargement (tsupport φ)
  have hK : IsCompact K := isCompact_mollifierEnlargement hc
  have hφ2 : MemLp φ 2 volume := hφ.continuous.memLp_of_hasCompactSupport hc
  have hdφ2 := memLp_volume_compact_coordinateDerivative hφ hc i
  have hb2 : MemLp (K.indicator b) 2 volume :=
    (memLp_indicator_iff_restrict hK.measurableSet.nullMeasurableSet).mpr (hb K hK)
  have ht := tendsto_integral_mul_of_eLpNorm_sub_tendsto_zero
    (fun k => (contDiff_coordinateDerivative
      ((mollify_contDiff hφ.continuous.locallyIntegrable k).of_le (by simp) : ContDiff ℝ 1 (mollify k φ))
      (m := 0) (by norm_num) i).continuous.memLp_of_hasCompactSupport
        (hasCompactSupport_coordinateDerivative (hasCompactSupport_mollify hc k) i))
    hdφ2 hb2 (eLpNorm_mollify_coordinateDerivative_sub_tendsto_zero hφ hφ2 i hdφ2)
  have heq {g : Space n → ℝ} (hgs : tsupport g ⊆ K) :
      (∫ x, K.indicator b x*g x) = ∫ x, b x*g x := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only
      by_cases hx : x ∈ K
      · rw [indicator_of_mem hx]
      · have hgx : g x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hgs h))
        rw [hgx,mul_zero,mul_zero]
  have hlim : tsupport (coordinateDerivative φ i) ⊆ K :=
    (tsupport_coordinateDerivative_subset φ i).trans (subset_mollifierEnlargement _)
  have hk (k : ℕ) : tsupport (coordinateDerivative (mollify k φ) i) ⊆ K :=
    (tsupport_coordinateDerivative_subset _ i).trans (tsupport_mollify_subset hc k)
  simpa only [heq hlim,heq (hk _)] using ht

/-- A genuine divergence identity with locally L2 coefficients extends from
 compact C1 tests to compact locally Lipschitz tests and their actual a.e. derivatives. -/
theorem integral_divergence_zero_of_locallyLipschitz_test
    {A : Fin n → Space n → ℝ}
    (hA : ∀ i, ∀ K : Set (Space n), IsCompact K → MemLp (A i) 2 (volume.restrict K))
    (hdiv : ∀ φ : Space n → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      (∑ i, ∫ x, A i x*coordinateDerivative φ i x) = 0)
    {φ : Space n → ℝ} (hφ : LocallyLipschitz φ) (hc : HasCompactSupport φ) :
    (∑ i, ∫ x, A i x*coordinateDerivative φ i x) = 0 := by
  have hi (i : Fin n) := tendsto_integral_mul_coordinateDerivative_mollify_of_localL2 hφ hc (hA i) i
  have hlim := tendsto_finsetSum Finset.univ (fun i _ => hi i)
  have hzero : (fun k => ∑ i, ∫ x, A i x*coordinateDerivative (mollify k φ) i x) = fun _ : ℕ => (0 : ℝ) := by
    funext k
    exact hdiv _ ((mollify_contDiff hφ.continuous.locallyIntegrable k).of_le (by simp))
      (hasCompactSupport_mollify hc k)
  rw [hzero] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

end KLS
end

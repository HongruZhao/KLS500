import KLS.NormalizedRadialMeanValue

open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff NNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

lemma normalizedRadialProfile_le_mass_inv (n : ℕ) (s : ℝ) :
    normalizedRadialProfile n s ≤ (radialKernelMass n)⁻¹ := by
  have hh := mul_le_mul_of_nonneg_right (radialBaseBump.le_one (x := s))
    (inv_nonneg.mpr (radialKernelMass_pos n).le)
  simpa only [normalizedRadialProfile, one_mul] using hh

lemma normalizedRadialKernel_le (c x : Space n) {t : ℝ} (ht : 0 < t) :
    radialAverageKernel (normalizedRadialProfile n) c t x ≤ (radialKernelMass n)⁻¹ / t ^ n :=
  div_le_div_of_nonneg_right (normalizedRadialProfile_le_mass_inv n _) (pow_nonneg ht.le n)

lemma continuous_normalizedRadialKernel (c : Space n) (t : ℝ) :
    Continuous (radialAverageKernel (normalizedRadialProfile n) c t) :=
  (contDiff_radialAverageKernel (normalizedRadialProfile_contDiff n) c t).continuous

lemma hasCompactSupport_normalizedRadialKernel (c : Space n) {t : ℝ} (ht : 0 < t) :
    HasCompactSupport (radialAverageKernel (normalizedRadialProfile n) c t) :=
  (isCompact_closedBall c t).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_radialAverageKernel_subset_closedBall (fun _ hs => normalizedRadialProfile_eq_zero n hs) c ht)

lemma closedBall_subset_centered_closedBall {c : Space n} {r s t : ℝ}
    (hc : c ∈ closedBall (0 : Space n) r) (hst : r + t ≤ s) :
    closedBall c t ⊆ closedBall (0 : Space n) s := by
  intro x hx
  have hh := dist_triangle x c (0 : Space n)
  change dist c 0 ≤ r at hc
  change dist x c ≤ t at hx
  change dist x 0 ≤ s
  linarith

lemma normalizedRadialKernel_tsupport_subset_centered_closedBall {c : Space n} {r s t : ℝ}
    (hc : c ∈ closedBall (0 : Space n) r) (ht : 0 < t) (hst : r + t ≤ s) :
    tsupport (radialAverageKernel (normalizedRadialProfile n) c t) ⊆ closedBall (0 : Space n) s :=
  (tsupport_radialAverageKernel_subset_closedBall (fun _ hs => normalizedRadialProfile_eq_zero n hs) c ht).trans
    (closedBall_subset_centered_closedBall hc hst)

end KLS
end

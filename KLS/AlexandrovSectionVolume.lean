import KLS.ConvexSectionNormalization
import KLS.SubgradientOscillation
import KLS.SubgradientAffineNormalization

/-! An actual section-volume estimate from a lower Alexandrov density.
Maximal-simplex affine normalization and the elementary interior slope bound
give the estimate directly. There is no assumed John theorem, PDE regularity,
or determinant formula for a nonsmooth Hessian. -/

open MeasureTheory InnerProductSpace Set Metric
open scoped Topology NNReal ENNReal

noncomputable section
namespace KLS

variable {n : ℕ}

theorem alexandrov_normalized_density_bound {u : Space n → ℝ} {K : Set (Space n)}
    (hK : IsCompact K) (hc : Convex ℝ K) (hne : (interior K).Nonempty)
    {h : ℝ} (hh : 0 ≤ h) (hosc : ∀ x ∈ K, -h ≤ u x ∧ u x ≤ 0)
    {κ : ℝ≥0∞}
    (hlower : ∀ S : Set (Space n), IsCompact S → S ⊆ K →
      κ * volume S ≤ volume (convexSubgradientImage u S)) :
    ∃ e : Space n ≃ᴬ[ℝ] Space n,
      closedBall 0 1 ⊆ e '' K ∧
      e '' K ⊆ closedBall 0 (2 * ((n : ℝ) + 1) ^ 3) ∧
      κ * (ENNReal.ofReal |LinearMap.det e.symm.linear.toLinearMap|) ^ 2 ≤
        ENNReal.ofReal ((4 * h) ^ n) := by
  obtain ⟨e, heinner, heouter⟩ := exists_ball_affine_normalization hK hc hne
  refine ⟨e, heinner, heouter, ?_⟩
  let d : ℝ≥0∞ := ENNReal.ofReal |LinearMap.det e.symm.linear.toLinearMap|
  let B : Set (Space n) := closedBall 0 (1 / 2)
  have hpre (x : Space n) (hx : x ∈ closedBall 0 1) : e.symm x ∈ K := by
    obtain ⟨y, hy, hxy⟩ := heinner hx
    rw [← hxy, e.symm_apply_apply]
    exact hy
  have hSsub : e.symm '' B ⊆ K := by
    rintro x ⟨y, hy, rfl⟩
    exact hpre y (closedBall_subset_closedBall (by norm_num : (1 / 2 : ℝ) ≤ 1) hy)
  have hScompact : IsCompact (e.symm '' B) := (isCompact_closedBall _ _).image e.symm.continuous
  have hmass := hlower (e.symm '' B) hScompact hSsub
  rw [volume_image_continuousAffineEquiv] at hmass
  have hmass' : (κ * d ^ 2) * volume B ≤
      volume (convexSubgradientImage (fun x => u (e.symm x)) B) := by
    rw [volume_convexSubgradientImage_continuousAffineEquiv]
    change (κ * d ^ 2) * volume B ≤ d * volume (convexSubgradientImage u (e.symm '' B))
    calc
      _ = d * (κ * (d * volume B)) := by ring
      _ ≤ _ := mul_le_mul_right hmass d
  exact alexandrov_density_le_of_unit_ball_oscillation hh
    (fun x hx => hosc _ (hpre x hx)) hmass'

/-- The volume of a convex section is bounded by its oscillation and its
lower Alexandrov density, with an explicit dimension-only factor. -/
theorem alexandrov_section_volume_bound {u : Space n → ℝ} {K : Set (Space n)}
    (hK : IsCompact K) (hc : Convex ℝ K) (hne : (interior K).Nonempty)
    {h : ℝ} (hh : 0 ≤ h) (hosc : ∀ x ∈ K, -h ≤ u x ∧ u x ≤ 0)
    {κ : ℝ≥0∞}
    (hlower : ∀ S : Set (Space n), IsCompact S → S ⊆ K →
      κ * volume S ≤ volume (convexSubgradientImage u S)) :
    κ * (volume K) ^ 2 ≤ ENNReal.ofReal ((4 * h) ^ n) *
      (volume (closedBall (0 : Space n) (2 * ((n : ℝ) + 1) ^ 3))) ^ 2 := by
  obtain ⟨e, _, heouter, hκ⟩ := alexandrov_normalized_density_bound hK hc hne hh hosc hlower
  let d : ℝ≥0∞ := ENNReal.ofReal |LinearMap.det e.symm.linear.toLinearMap|
  let V : ℝ≥0∞ := volume (closedBall (0 : Space n) (2 * ((n : ℝ) + 1) ^ 3))
  have hKimage : e.symm '' (e '' K) = K := by
    rw [image_image]
    simp only [e.symm_apply_apply]
    exact Set.image_id K
  have hvol : volume K ≤ d * V := by
    calc
      _ = volume (e.symm '' (e '' K)) := congrArg volume hKimage.symm
      _ = d * volume (e '' K) := volume_image_continuousAffineEquiv e.symm _
      _ ≤ d * V := mul_le_mul_right (measure_mono heouter) d
  calc
    _ ≤ κ * (d * V) ^ 2 := mul_le_mul_right (pow_le_pow_left' hvol 2) κ
    _ = (κ * d ^ 2) * V ^ 2 := by ring
    _ ≤ ENNReal.ofReal ((4 * h) ^ n) * V ^ 2 := mul_le_mul_left hκ _

end KLS
end

#print axioms KLS.alexandrov_normalized_density_bound
#print axioms KLS.alexandrov_section_volume_bound

import KLS.AlexandrovSectionVolume
import KLS.SubgradientDirectionalEstimate

/-!
# Normalized section width control

Two-sided Alexandrov volume bounds control the supporting width at every
negative point after the actual affine section normalization. The Jacobian
appears twice and cancels between the lower and upper density bounds. This
is a geometric input to localization, not a strict-convexity theorem.
-/

open MeasureTheory InnerProductSpace Set Metric
open scoped Topology ENNReal

noncomputable section
namespace KLS

variable {n : ℕ}

/-- An upper Alexandrov density bound transforms with the square of the
inverse affine Jacobian, on every open set in the normalized domain. -/
theorem subgradient_volume_upper_affine
    {u : Space n → ℝ} {K : Set (Space n)} {b : ℝ≥0∞}
    (hupper : ∀ S : Set (Space n), IsOpen S → S ⊆ K →
      volume (convexSubgradientImage u S) ≤ b * volume S)
    (e : Space n ≃ᴬ[ℝ] Space n) {S : Set (Space n)}
    (hS : IsOpen S) (hSK : S ⊆ e '' K) :
    volume (convexSubgradientImage (fun z => u (e.symm z)) S) ≤
      (b * (ENNReal.ofReal |LinearMap.det e.symm.linear.toLinearMap|) ^ 2) *
        volume S := by
  let d : ℝ≥0∞ := ENNReal.ofReal |LinearMap.det e.symm.linear.toLinearMap|
  have hpre : e.symm '' S ⊆ K := by
    rintro z ⟨y, hy, rfl⟩
    obtain ⟨x, hx, rfl⟩ := hSK hy
    simpa only [e.symm_apply_apply] using hx
  have hopen : IsOpen (e.symm '' S) := e.symm.toHomeomorph.isOpenMap S hS
  have hm := hupper (e.symm '' S) hopen hpre
  rw [volume_image_continuousAffineEquiv] at hm
  rw [volume_convexSubgradientImage_continuousAffineEquiv]
  change d * volume (convexSubgradientImage u (e.symm '' S)) ≤ (b * d ^ 2) * volume S
  calc
    _ ≤ d * (b * (d * volume S)) := mul_le_mul_right hm d
    _ = _ := by ring

/-- Actual affine normalization gives a dimension-only containing radius
and a supporting-width inequality with the original density ratio. No
smoothness or classical determinant of the potential is assumed. -/
theorem exists_normalization_with_directional_width_control
    {u : Space n → ℝ} {K : Set (Space n)}
    (hK : IsCompact K) (hc : Convex ℝ K) (hne : (interior K).Nonempty)
    (hucont : Continuous u) (huconvex : ConvexOn ℝ univ u)
    (hboundary : ∀ z ∈ frontier K, 0 ≤ u z)
    {h : ℝ} (hh : 0 ≤ h) (hosc : ∀ z ∈ K, -h ≤ u z ∧ u z ≤ 0)
    {a b : ℝ≥0∞}
    (hlower : ∀ S : Set (Space n), IsCompact S → S ⊆ K →
      a * volume S ≤ volume (convexSubgradientImage u S))
    (hupper : ∀ S : Set (Space n), IsOpen S → S ⊆ K →
      volume (convexSubgradientImage u S) ≤ b * volume S) :
    ∃ e : Space n ≃ᴬ[ℝ] Space n,
      closedBall 0 1 ⊆ e '' K ∧
      e '' K ⊆ closedBall 0 (2 * ((n : ℝ) + 1) ^ 3) ∧
      ∀ (_i : Fin n) (x v : Space n) (δ : ℝ), x ∈ e '' K → u (e.symm x) < 0 →
        ‖v‖ = 1 → 0 < δ →
        (∀ z ∈ e '' K, inner ℝ v (z - x) ≤ δ) →
        a * (ENNReal.ofReal (-u (e.symm x) / (2 * δ)) *
          ENNReal.ofReal (-u (e.symm x) / (n * (4 * ((n : ℝ) + 1) ^ 3))) ^ (n - 1)) ≤
          b * ENNReal.ofReal ((4 * h) ^ n) *
            volume (closedBall (0 : Space n) (2 * ((n : ℝ) + 1) ^ 3)) := by
  obtain ⟨e, heinner, heouter, hscale⟩ :=
    alexandrov_normalized_density_bound hK hc hne hh hosc hlower
  refine ⟨e, heinner, heouter, ?_⟩
  intro i x v δ hx hux hv hδ hwidth
  let R : ℝ := 2 * ((n : ℝ) + 1) ^ 3
  let d : ℝ≥0∞ := ENNReal.ofReal |LinearMap.det e.symm.linear.toLinearMap|
  have hR : 0 < R := by dsimp [R]; positivity
  have hK' : IsCompact (e '' K) := hK.image e.continuous
  have hcont' : Continuous (fun z => u (e.symm z)) := hucont.comp e.symm.continuous
  have hconvex' : ConvexOn ℝ univ (fun z => u (e.symm z)) := by
    refine ⟨convex_univ, ?_⟩
    intro z _ w _ c f hc hf hcf
    have hcombo : e.symm (c • z + f • w) = c • e.symm z + f • e.symm w := by
      simpa only [AffineEquiv.coe_toAffineMap, ContinuousAffineEquiv.coe_coe] using
        Convex.combo_affine_apply (f := e.symm.toAffineEquiv.toAffineMap) (x := z) (y := w) hcf
    change u (e.symm (c • z + f • w)) ≤ c • u (e.symm z) + f • u (e.symm w)
    rw [hcombo]
    exact huconvex.2 (mem_univ _) (mem_univ _) hc hf hcf
  have hboundary' : ∀ z ∈ frontier (e '' K), 0 ≤ u (e.symm z) := by
    intro z hz
    have himg := e.toHomeomorph.image_frontier K
    change e '' frontier K = frontier (e '' K) at himg
    rw [← himg] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    simpa only [e.symm_apply_apply] using hboundary y hy
  have hnorm : ∀ z ∈ e '' K, ‖z - x‖ ≤ 2 * R := by
    intro z hz
    have hzR : ‖z‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using heouter hz
    have hxR : ‖x‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using heouter hx
    calc
      _ ≤ ‖z‖ + ‖x‖ := norm_sub_le _ _
      _ ≤ 2 * R := by linarith
  have hpolar := directional_alexandrov_maximum_estimate i hK' hcont' hconvex'
    hboundary' hx hux hv hδ (by positivity : 0 < 2 * R) hwidth hnorm
  have hmass := subgradient_volume_upper_affine hupper e isOpen_interior interior_subset
  have hvol : volume (interior (e '' K)) ≤ volume (closedBall (0 : Space n) R) :=
    measure_mono (interior_subset.trans heouter)
  have hbound := hpolar.trans (hmass.trans (mul_le_mul_right hvol (b * d ^ 2)))
  change _ ≤ (b * d ^ 2) * volume (closedBall (0 : Space n) R) at hbound
  have hscaled := mul_le_mul_right hbound a
  have hR2 : 2 * R = 4 * ((n : ℝ) + 1) ^ 3 := by dsimp [R]; ring
  rw [hR2] at hscaled
  calc
    _ ≤ a * ((b * d ^ 2) * volume (closedBall (0 : Space n) R)) := hscaled
    _ = b * (a * d ^ 2) * volume (closedBall (0 : Space n) R) := by ring
    _ ≤ b * ENNReal.ofReal ((4 * h) ^ n) * volume (closedBall (0 : Space n) R) :=
      mul_le_mul_left (mul_le_mul_right hscale b) _
    _ = _ := rfl

end KLS
end

#print axioms KLS.subgradient_volume_upper_affine
#print axioms KLS.exists_normalization_with_directional_width_control

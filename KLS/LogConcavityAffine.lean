import KLS.DefinitionBridges

/-!
# Affine transport for compact-set log-concavity

These lemmas use exactly `measureLogConcave` from the full measure-based KLS
class. They prove its invariance under invertible continuous affine changes
of coordinates, including the centering and whitening transformations used
in regular approximation. No density or absolute continuity is assumed.
-/

open MeasureTheory Set
open scoped ENNReal

namespace KLS

theorem affineMap_affineCombination {n m : ℕ}
    (e : Space n →ᵃ[ℝ] Space m) (t : ℝ) (x y : Space n) :
    e (t • x + (1 - t) • y) = t • e x + (1 - t) • e y := by
  simpa only [AffineMap.lineMap_apply_module, add_comm] using e.apply_lineMap y x t

/-- Affine maps commute with compact-set Minkowski interpolation. -/
theorem affineMap_image_affineSetCombination {n m : ℕ}
    (e : Space n →ᵃ[ℝ] Space m) (t : ℝ) (E F : Set (Space n)) :
    e '' affineSetCombination t E F = affineSetCombination t (e '' E) (e '' F) := by
  ext z
  constructor
  · rintro ⟨w, ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩, rfl⟩
    exact ⟨(e x, e y), ⟨⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩⟩,
      (affineMap_affineCombination e t x y).symm⟩
  · rintro ⟨⟨u, v⟩, ⟨⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩⟩, rfl⟩
    exact ⟨t • x + (1 - t) • y, ⟨(x, y), ⟨hx, hy⟩, rfl⟩,
      affineMap_affineCombination e t x y⟩

theorem affineEquiv_preimage_affineSetCombination {n m : ℕ}
    (e : Space n ≃ᴬ[ℝ] Space m) (t : ℝ) (E F : Set (Space m)) :
    e ⁻¹' affineSetCombination t E F =
      affineSetCombination t (e ⁻¹' E) (e ⁻¹' F) := by
  have h := affineMap_image_affineSetCombination e.symm.toAffineEquiv.toAffineMap t E F
  change e.symm '' affineSetCombination t E F =
    affineSetCombination t (e.symm '' E) (e.symm '' F) at h
  simpa only [ContinuousAffineEquiv.image_symm] using h

/-- Invertible affine pushforwards preserve the full compact-set definition
of log-concavity. -/
theorem measureLogConcave.map_continuousAffineEquiv {n m : ℕ}
    {μ : Measure (Space n)} (hμ : measureLogConcave μ)
    (e : Space n ≃ᴬ[ℝ] Space m) : measureLogConcave (μ.map e) := by
  intro E F hE hF t ht0 ht1
  rw [Measure.map_apply e.continuous.measurable hE.measurableSet,
    Measure.map_apply e.continuous.measurable hF.measurableSet,
    Measure.map_apply e.continuous.measurable (measurableSet_affineSetCombination t hE hF),
    affineEquiv_preimage_affineSetCombination]
  exact hμ (e ⁻¹' E) (e ⁻¹' F)
    (e.toHomeomorph.isCompact_preimage.mpr hE)
    (e.toHomeomorph.isCompact_preimage.mpr hF) t ht0 ht1

/-- The affine change is reversible, so preservation is an equivalence. -/
theorem measureLogConcave_map_continuousAffineEquiv_iff {n m : ℕ}
    {μ : Measure (Space n)} (e : Space n ≃ᴬ[ℝ] Space m) :
    measureLogConcave (μ.map e) ↔ measureLogConcave μ := by
  constructor
  · intro h
    have hback := h.map_continuousAffineEquiv e.symm
    rw [Measure.map_map e.symm.continuous.measurable e.continuous.measurable] at hback
    have hid : (fun x => e.symm (e x)) = id := funext e.symm_apply_apply
    rw [Function.comp_def, hid, Measure.map_id] at hback
    exact hback
  · exact fun h => h.map_continuousAffineEquiv e

end KLS

#print axioms KLS.affineMap_image_affineSetCombination
#print axioms KLS.measureLogConcave.map_continuousAffineEquiv
#print axioms KLS.measureLogConcave_map_continuousAffineEquiv_iff

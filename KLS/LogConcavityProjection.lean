import KLS.LogConcavityTails
import KLS.LogConcavityAffine

/-!
# Affine images and marginals of compact-set log-concave measures

Inner regularity extends the compact-set inequality to arbitrary measurable
inputs in inclusion form. The output needs no Minkowski-sum measurability
assumption. This proves preservation under all continuous affine maps,
including projections and maps whose image lies in a proper affine subspace.
-/

open MeasureTheory Set
open scoped ENNReal

namespace KLS

private theorem rpow_iSup_pos {ι : Sort*} (f : ι → ℝ≥0∞) {t : ℝ} (ht : 0 < t) :
    (⨆ i, f i) ^ t = ⨆ i, (f i) ^ t :=
  (ENNReal.orderIsoRpow t ht).map_iSup f

/-- Both inputs may be arbitrary measurable sets. An inclusion into a target
set is sufficient; no measurable Minkowski sum is assumed. -/
theorem measureLogConcave.le_measure_of_measurable_interpolation
    {n : ℕ} {μ : Measure (Space n)} [IsFiniteMeasure μ]
    (hμ : measureLogConcave μ) {E F A : Set (Space n)}
    (hE : MeasurableSet E) (hF : MeasurableSet F)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hsub : affineSetCombination t E F ⊆ A) :
    (μ E) ^ t * (μ F) ^ (1 - t) ≤ μ A := by
  conv_lhs => arg 1; arg 1; rw [hE.measure_eq_iSup_isCompact μ]
  simp_rw [rpow_iSup_pos _ ht0, ENNReal.iSup_mul]
  refine iSup_le fun K => iSup_le fun hKE => iSup_le fun hK => ?_
  apply hμ.le_measure_of_compact_measurable_interpolation hK hF ht0 ht1
  rintro z ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
  exact hsub ⟨(x, y), ⟨hKE hx, hy⟩, rfl⟩

/-- All continuous affine images of finite compact-set log-concave measures
are compact-set log-concave. No injectivity or surjectivity is required. -/
theorem measureLogConcave.map_continuousAffineMap {n m : ℕ}
    {μ : Measure (Space n)} [IsFiniteMeasure μ] (hμ : measureLogConcave μ)
    (f : Space n →ᴬ[ℝ] Space m) : measureLogConcave (μ.map f) := by
  intro E F hE hF t ht0 ht1
  rw [Measure.map_apply f.continuous.measurable hE.measurableSet,
    Measure.map_apply f.continuous.measurable hF.measurableSet,
    Measure.map_apply f.continuous.measurable (measurableSet_affineSetCombination t hE hF)]
  apply hμ.le_measure_of_measurable_interpolation
    (f.continuous.measurable hE.measurableSet) (f.continuous.measurable hF.measurableSet) ht0 ht1
  rintro z ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
  exact ⟨(f x, f y), ⟨hx, hy⟩,
    (affineMap_affineCombination f.toAffineMap t x y).symm⟩

end KLS

#print axioms KLS.measureLogConcave.le_measure_of_measurable_interpolation
#print axioms KLS.measureLogConcave.map_continuousAffineMap

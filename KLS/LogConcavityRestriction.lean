import KLS.DefinitionBridges

/-!+# Closed convex restriction and normalization

These operations preserve the exact compact-set measure definition. The
measure need not have a density. No general class-equivalence theorem is used.
-/

open MeasureTheory Set
open scoped ENNReal

namespace KLS

theorem measureLogConcave.restrict_closed_convex {n : ℕ}
    {μ : Measure (Space n)} (hμ : measureLogConcave μ) {S : Set (Space n)}
    (hS : IsClosed S) (hconv : Convex ℝ S) : measureLogConcave (μ.restrict S) := by
  intro E F hE hF t ht0 ht1
  rw [Measure.restrict_apply hE.measurableSet, Measure.restrict_apply hF.measurableSet,
    Measure.restrict_apply (measurableSet_affineSetCombination t hE hF)]
  apply (hμ (E ∩ S) (F ∩ S) (hE.inter_right hS) (hF.inter_right hS) t ht0 ht1).trans
  apply measure_mono
  rintro z ⟨⟨x, y⟩, ⟨⟨hxE, hxS⟩, ⟨hyF, hyS⟩⟩, rfl⟩
  exact ⟨⟨(x, y), ⟨hxE, hyF⟩, rfl⟩,
    hconv hxS hyS ht0.le (sub_nonneg.mpr ht1.le) (by ring)⟩

theorem measureLogConcave.smul {n : ℕ} {μ : Measure (Space n)}
    (hμ : measureLogConcave μ) (c : ℝ≥0∞) : measureLogConcave (c • μ) := by
  intro E F hE hF t ht0 ht1
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [ENNReal.mul_rpow_of_nonneg _ _ ht0.le,
    ENNReal.mul_rpow_of_nonneg _ _ (sub_nonneg.mpr ht1.le)]
  have hexp : c ^ t * c ^ (1 - t) = c := by
    rw [← ENNReal.rpow_add_of_nonneg t (1 - t) ht0.le (sub_nonneg.mpr ht1.le)]
    simp
  calc
    c ^ t * (μ E) ^ t * (c ^ (1 - t) * (μ F) ^ (1 - t)) =
        (c ^ t * c ^ (1 - t)) * ((μ E) ^ t * (μ F) ^ (1 - t)) := by ac_rfl
    _ = c * ((μ E) ^ t * (μ F) ^ (1 - t)) := by rw [hexp]
    _ ≤ c * μ (affineSetCombination t E F) :=
      mul_le_mul_right (hμ E F hE hF t ht0 ht1) c

theorem measureLogConcave.cond_closed_convex {n : ℕ}
    {μ : Measure (Space n)} (hμ : measureLogConcave μ) {S : Set (Space n)}
    (hS : IsClosed S) (hconv : Convex ℝ S) :
    measureLogConcave (ProbabilityTheory.cond μ S) :=
  (hμ.restrict_closed_convex hS hconv).smul _

end KLS

#print axioms KLS.measureLogConcave.restrict_closed_convex
#print axioms KLS.measureLogConcave.smul
#print axioms KLS.measureLogConcave.cond_closed_convex

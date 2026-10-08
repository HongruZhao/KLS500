import KLS.ExponentialCompactLogConcavity
import KLS.ExponentialPoincare

/-!
# A sharp lower-bound witness in the exact compact-set admissible class

The independently proved scalar compact-set inequality is transported by
the actual centered exponential embedding. Combining that membership with
the existing exact Poincaré constant gives a certified universal lower bound
of four. No universal upper bound is asserted.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

noncomputable section
namespace KLS.CenteredExponential

def embeddingHomeomorph : ℝ ≃ₜ Space 1 where
  toEquiv := embeddingEquiv.toEquiv
  continuous_toFun := continuous_embedding
  continuous_invFun := by
    change Continuous (fun x : Space 1 => x 0 + 1)
    fun_prop

theorem embedding_affineCombination (x y t : ℝ) :
    embedding (t * x + (1 - t) * y) = t • embedding x + (1 - t) • embedding y := by
  ext i
  simp only [embedding_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

theorem embedding_preimage_affineSetCombination (E F : Set (Space 1)) (t : ℝ) :
    embedding ⁻¹' affineSetCombination t E F =
      realAffineSetCombination t (embedding ⁻¹' E) (embedding ⁻¹' F) := by
  ext z
  constructor
  · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, hxy⟩
    refine ⟨(embeddingEquiv.symm x, embeddingEquiv.symm y), ⟨?_, ?_⟩, ?_⟩
    · change embeddingEquiv (embeddingEquiv.symm x) ∈ E
      rw [embeddingEquiv.apply_symm_apply]
      exact hx
    · change embeddingEquiv (embeddingEquiv.symm y) ∈ F
      rw [embeddingEquiv.apply_symm_apply]
      exact hy
    · apply embeddingEquiv.injective
      change embedding (t * embeddingEquiv.symm x + (1 - t) * embeddingEquiv.symm y) = embedding z
      rw [embedding_affineCombination]
      change t • embeddingEquiv (embeddingEquiv.symm x) +
        (1 - t) • embeddingEquiv (embeddingEquiv.symm y) = embedding z
      rw [embeddingEquiv.apply_symm_apply, embeddingEquiv.apply_symm_apply]
      exact hxy
  · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
    exact ⟨(embedding x, embedding y), ⟨hx, hy⟩, (embedding_affineCombination x y t).symm⟩

/-- Compact-set log-concavity of the frozen, concrete centered exponential law. -/
theorem measureLogConcave : KLS.measureLogConcave measure := by
  change KLS.measureLogConcave ((expMeasure 1).map embedding)
  intro E F hE hF t ht0 ht1
  rw [Measure.map_apply continuous_embedding.measurable hE.measurableSet,
    Measure.map_apply continuous_embedding.measurable hF.measurableSet,
    Measure.map_apply continuous_embedding.measurable (measurableSet_affineSetCombination t hE hF),
    embedding_preimage_affineSetCombination]
  exact expMeasure_one_compact_logConcave
    (embeddingHomeomorph.isCompact_preimage.mpr hE)
    (embeddingHomeomorph.isCompact_preimage.mpr hF) ht0 ht1

/-- Membership now uses exactly the full compact-set admissible predicate. -/
theorem admissible : admissibleMeasure measure :=
  ⟨inferInstance, measureLogConcave, isIsotropic⟩

theorem admissible_and_poincareConstant_eq_four :
    admissibleMeasure measure ∧ poincareConstant measure = 4 :=
  ⟨admissible, poincareConstant_eq_four⟩

end KLS.CenteredExponential

namespace KLS

/-- A certified lower bound on the universal optimum over the entire
compact-set admissible class. It does not imply a matching upper bound. -/
theorem four_le_universalPoincareConstant : 4 ≤ universalPoincareConstant := by
  rw [← CenteredExponential.poincareConstant_eq_four]
  exact poincareConstant_le_universal (by norm_num : 1 ≤ 1) CenteredExponential.admissible

end KLS
end

#print axioms KLS.CenteredExponential.measureLogConcave
#print axioms KLS.CenteredExponential.admissible_and_poincareConstant_eq_four
#print axioms KLS.four_le_universalPoincareConstant

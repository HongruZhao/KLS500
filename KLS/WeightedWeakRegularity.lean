import KLS.WeightedClassicalLiouville
import KLS.WeightedDiffusionLiouville

/-!
# The remaining weak-to-classical regularity obligation

Classical weighted L² Liouville is proved separately. This file names exactly
the additional weak-solution regularity needed for diffusion-range density,
and proves the reduction. It does not assert that regularity hypothesis.
The domain is all of Euclidean space, for a finite real potential.
-/

open MeasureTheory InnerProductSpace Filter
open scoped ContDiff

noncomputable section
namespace KLS

variable {n : ℕ}

/-- Every actual weighted-L² weak harmonic function has an a.e. equal classical C² representative.
This elliptic regularity property is an explicit remaining hypothesis, not a theorem here. -/
def WeakDiffusionRegularity (φ : Space n → ℝ) : Prop :=
  ∀ u : Lp ℝ 2 (potentialMeasure φ),
    (∀ g : Space n → ℝ, ContDiff ℝ 3 g → HasCompactSupport g →
      (∫ x, u x * weightedDiffusion φ g x ∂potentialMeasure φ) = 0) →
    ∃ h : Space n → ℝ, ContDiff ℝ 2 h ∧
      (u : Space n → ℝ) =ᵐ[potentialMeasure φ] h ∧
        ∀ x, weightedDiffusion φ h x = 0

/-- The proved classical theorem reduces weak Liouville to the visible regularity obligation. -/
theorem weakDiffusionLiouville_of_weakDiffusionRegularity {φ : Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hreg : WeakDiffusionRegularity φ) : WeakDiffusionLiouville φ := by
  intro u hu
  obtain ⟨h, hh, hueq, hharm⟩ := hreg u hu
  have hL2 : MemLp h 2 (potentialMeasure φ) := (memLp_congr_ae hueq).mp (Lp.memLp u)
  obtain ⟨c, hc⟩ := classical_weighted_liouville hφ hh hL2 hharm
  exact ⟨c, hueq.trans (Eventually.of_forall hc)⟩

/-- Genuine norm density follows if the separate elliptic regularity obligation is supplied. -/
theorem diffusionRangeDense_of_weakDiffusionRegularity {φ : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hreg : WeakDiffusionRegularity φ) : DiffusionRangeDense φ :=
  diffusionRangeDense_of_weakDiffusionLiouville hφ
    (weakDiffusionLiouville_of_weakDiffusionRegularity (hφ.of_le (by norm_num)) hreg)

end KLS
end

#print axioms KLS.weakDiffusionLiouville_of_weakDiffusionRegularity
#print axioms KLS.diffusionRangeDense_of_weakDiffusionRegularity

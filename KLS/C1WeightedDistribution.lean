import KLS.C1DiffusionCompact

/-!
# C¹ potential: C1WeightedDistribution

This extension uses the actual diffusion and weighted L² representatives.
Only first derivatives of the source potential are required.
-/

open MeasureTheory InnerProductSpace Set Filter ContinuousLinearMap
open scoped ContDiff ENNReal Convolution Topology

noncomputable section
namespace KLS
variable {n : ℕ}

theorem weak_diffusion_unweighted_laplacian_C1 {φ : Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (u : Lp ℝ 2 (potentialMeasure φ))
    (hu : ∀ g : Space n → ℝ, ContDiff ℝ 3 g → HasCompactSupport g →
      (∫ x, u x * weightedDiffusion φ g x ∂potentialMeasure φ) = 0)
    {g : Space n → ℝ} (hg : ContDiff ℝ 3 g) (hc : HasCompactSupport g) :
    (∫ x, u x * Real.exp (-φ x) * coordinateLaplacian g x) =
      ∫ x, u x * Real.exp (-φ x) * inner ℝ (gradient φ x) (gradient g x) := by
  have hIlap : Integrable (fun x => u x * coordinateLaplacian g x) (potentialMeasure φ) :=
    (Lp.memLp u).integrable_mul
      (memLp_coordinateLaplacian_of_hasCompactSupport hφ.continuous
        (hg.of_le (by norm_num)) hc)
  have hIdiff : Integrable (fun x => u x * weightedDiffusion φ g x) (potentialMeasure φ) :=
    (Lp.memLp u).integrable_mul
      (memLp_weightedDiffusion_of_C1_hasCompactSupport hφ hg hc)
  have hIdrift : Integrable (fun x => u x * inner ℝ (gradient φ x) (gradient g x))
      (potentialMeasure φ) := by
    convert hIlap.sub hIdiff using 1
    funext x
    dsimp only [Pi.sub_apply, weightedDiffusion]
    ring
  have he := hu g hg hc
  have hsplit : (∫ x, u x * weightedDiffusion φ g x ∂potentialMeasure φ) =
      (∫ x, u x * coordinateLaplacian g x ∂potentialMeasure φ) -
        ∫ x, u x * inner ℝ (gradient φ x) (gradient g x) ∂potentialMeasure φ := by
    rw [← integral_sub hIlap hIdrift]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by dsimp [weightedDiffusion]; ring
  rw [hsplit, sub_eq_zero] at he
  rw [integral_potentialMeasure hφ.continuous.measurable,
    integral_potentialMeasure hφ.continuous.measurable] at he
  convert he using 1 <;> apply integral_congr_ae <;>
    exact Eventually.of_forall fun x => by dsimp only; ring

end KLS
end

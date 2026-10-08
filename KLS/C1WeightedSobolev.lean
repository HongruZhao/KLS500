import KLS.C1WeightedMollification
import KLS.WeightedLocalSobolev

/-!
# C¹ potential: C1WeightedSobolev

This extension uses the actual diffusion and weighted L² representatives.
Only first derivatives of the source potential are required.
-/

open MeasureTheory InnerProductSpace Set Filter ContinuousLinearMap
open scoped ContDiff ENNReal Convolution Topology

noncomputable section
namespace KLS
variable {n : ℕ}

theorem weighted_annihilator_localized_derivative_bound_C1 {φ χ : Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (u : Lp ℝ 2 (potentialMeasure φ))
    (hu : ∀ g : Space n → ℝ, ContDiff ℝ 3 g → HasCompactSupport g →
      (∫ x, u x * weightedDiffusion φ g x ∂potentialMeasure φ) = 0)
    (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k : ℕ, ∀ i : Fin n,
      (∫ x, coordinateDerivative (fun y => χ y * mollify k (densityWeightedFunction φ u) y) i x ^ 2) ≤ M := by
  apply exists_uniform_derivative_sq_compact_mul_mollify (F := densityWeightedFlux φ u) hχ hc
    (fun K hK => memLp_densityWeightedFunction_restrict hφ.continuous u hK)
    (fun i K hK => memLp_densityWeightedFlux_restrict (hφ.of_le (by norm_num)) u hK i)
  intro k x
  exact laplacian_mollified_weighted_distribution_C1 hφ u hu
    (κ := mollifierKernel n k) ((mollifierKernel_contDiff k).of_le (by simp))
    (mollifierKernel_hasCompactSupport k) x

theorem weighted_annihilator_cutoff_density_hasWeakDerivative_C1 {φ χ : Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (u : Lp ℝ 2 (potentialMeasure φ))
    (hu : ∀ g : Space n → ℝ, ContDiff ℝ 3 g → HasCompactSupport g →
      (∫ x, u x * weightedDiffusion φ g x ∂potentialMeasure φ) = 0)
    (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ) (i : Fin n) :
    ∃ g : Lp ℝ 2 (volume : Measure (Space n)),
      HasWeakCoordinateDerivative (fun x => χ x * densityWeightedFunction φ u x) i g := by
  have hv : ∀ K : Set (Space n), IsCompact K →
      MemLp (densityWeightedFunction φ u) 2 (volume.restrict K) :=
    fun K hK => memLp_densityWeightedFunction_restrict hφ.continuous u hK
  have hloc := locallyIntegrable_of_memLp_two_on_compacts hv
  have hU := memLp_compact_mul_of_local hχ.continuous hc hv
  have hconv := eLpNorm_compact_mul_mollify_sub_tendsto_zero hχ.continuous hc hv
  obtain ⟨M, hM, hb⟩ := weighted_annihilator_localized_derivative_bound_C1 hφ u hu hχ hc
  obtain ⟨g, -, hg⟩ := exists_weak_coordinateDerivative_of_approximation
    (f := fun k x => χ x * mollify k (densityWeightedFunction φ u) x)
    (fun k => hχ.mul ((mollify_contDiff hloc k).of_le (by simp)))
    (fun _ => hc.mul_right) hU hconv i hM (fun k => hb k i)
  exact ⟨g, hg⟩

theorem weighted_annihilator_compact_square_hasWeakDerivative_C1 {φ χ : Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (u : Lp ℝ 2 (potentialMeasure φ))
    (hu : ∀ g : Space n → ℝ, ContDiff ℝ 3 g → HasCompactSupport g →
      (∫ x, u x * weightedDiffusion φ g x ∂potentialMeasure φ) = 0)
    (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ) (i : Fin n) :
    ∃ g : Lp ℝ 2 (volume : Measure (Space n)),
      HasWeakCoordinateDerivative (fun x => χ x ^ 2 * u x) i g := by
  obtain ⟨g, hg⟩ := weighted_annihilator_cutoff_density_hasWeakDerivative_C1 hφ u hu hχ hc i
  have hloc : ∀ K : Set (Space n), IsCompact K →
      MemLp (densityWeightedFunction φ u) 2 (volume.restrict K) :=
    fun K hK => memLp_densityWeightedFunction_restrict hφ.continuous u hK
  have hf := memLp_compact_mul_of_local hχ.continuous hc hloc
  have hb : ContDiff ℝ 1 (fun x => χ x * Real.exp (φ x)) :=
    hχ.mul (hφ.of_le (by norm_num)).exp
  obtain ⟨G, hG⟩ := hg.compact_mul hf hb hc.mul_right
  have heq : (fun x => (χ x * Real.exp (φ x)) * (χ x * densityWeightedFunction φ u x)) =
      fun x => χ x ^ 2 * u x := by
    funext x
    dsimp [densityWeightedFunction]
    calc
      χ x * Real.exp (φ x) * (χ x * (u x * Real.exp (-φ x))) =
          χ x ^ 2 * u x * (Real.exp (φ x) * Real.exp (-φ x)) := by ring
      _ = χ x ^ 2 * u x := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
  rw [heq] at hG
  exact ⟨G, hG⟩

end KLS
end

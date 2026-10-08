import KLS.MollificationLocalization
import KLS.ForcedCaccioppoli

/-!
# Uniform gradients for localized mollified weighted annihilators

The distribution equation has already been mollified into a classical
Laplace-divergence equation. Forced Caccioppoli and actual local L² control
now give uniform global L² bounds for every derivative of χ·vε, where χ is
an arbitrary fixed compact C¹ cutoff. No weak derivative of the input is
assumed. This supplies the boundedness premise for weak-gradient extraction.
-/

open MeasureTheory InnerProductSpace Set Filter
open scoped ContDiff ENNReal Topology

noncomputable section
namespace KLS

variable {n : ℕ}

/-- Uniform derivatives of compactly localized mollifications of a divergence equation. -/
theorem exists_uniform_derivative_sq_compact_mul_mollify {χ v : Space n → ℝ}
    {F : Fin n → Space n → ℝ} (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ)
    (hv : ∀ K : Set (Space n), IsCompact K → MemLp v 2 (volume.restrict K))
    (hF : ∀ i, ∀ K : Set (Space n), IsCompact K → MemLp (F i) 2 (volume.restrict K))
    (heq : ∀ k x, coordinateLaplacian (mollify k v) x =
      -(∑ i, coordinateDerivative (mollify k (F i)) i x)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k : ℕ, ∀ i : Fin n,
      (∫ x, coordinateDerivative (fun y => χ y * mollify k v y) i x ^ 2) ≤ M := by
  have hvloc := locallyIntegrable_of_memLp_two_on_compacts hv
  have hFloc (i : Fin n) := locallyIntegrable_of_memLp_two_on_compacts (hF i)
  have hAex (i : Fin n) : ∃ A : ℝ, 0 ≤ A ∧ ∀ k : ℕ,
      (∫ x, coordinateDerivative χ i x ^ 2 * mollify k v x ^ 2) ≤ A :=
    exists_uniform_integral_sq_compact_mul_mollify
      (contDiff_coordinateDerivative hχ (m := 0) (by norm_num) i).continuous
      (hasCompactSupport_coordinateDerivative hc i) hv
  have hBex (i : Fin n) : ∃ B : ℝ, 0 ≤ B ∧ ∀ k : ℕ,
      (∫ x, χ x ^ 2 * mollify k (F i) x ^ 2) ≤ B :=
    exists_uniform_integral_sq_compact_mul_mollify hχ.continuous hc (hF i)
  choose A hA0 hAb using hAex
  choose B hB0 hBb using hBex
  refine ⟨22 * (∑ i, A i) + 8 * (∑ i, B i),
    add_nonneg (mul_nonneg (by norm_num) (Finset.sum_nonneg (fun i _ => hA0 i)))
      (mul_nonneg (by norm_num) (Finset.sum_nonneg (fun i _ => hB0 i))), ?_⟩
  intro k i
  have hhk : ContDiff ℝ 2 (mollify k v) := (mollify_contDiff hvloc k).of_le (by simp)
  have hFk (j : Fin n) : ContDiff ℝ 1 (mollify k (F j)) :=
    (mollify_contDiff (hFloc j) k).of_le (by simp)
  let f : Space n → ℝ := fun x => χ x * mollify k v x
  have hf : ContDiff ℝ 1 f := hχ.mul (hhk.of_le (by norm_num))
  have hfc : HasCompactSupport f := hc.mul_right
  have hdcχ (j : Fin n) := (contDiff_coordinateDerivative hχ (m := 0) (by norm_num) j).continuous
  have hdch (j : Fin n) := (contDiff_coordinateDerivative hhk (m := 0) (by norm_num) j).continuous
  have hEi (j : Fin n) : Integrable (fun x => χ x ^ 2 * coordinateDerivative (mollify k v) j x ^ 2)
      volume :=
    ((hχ.continuous.pow 2).mul ((hdch j).pow 2)).integrable_of_hasCompactSupport
      (by simpa [pow_two, Pi.mul_def] using hc.mul_right.mul_right)
  have hAi (j : Fin n) : Integrable (fun x => mollify k v x ^ 2 * coordinateDerivative χ j x ^ 2)
      volume :=
    ((hhk.continuous.pow 2).mul ((hdcχ j).pow 2)).integrable_of_hasCompactSupport
      (by simpa [pow_two, Pi.mul_def] using
        (hasCompactSupport_coordinateDerivative hc j).mul_right.mul_left)
  have hBi (j : Fin n) : Integrable (fun x => χ x ^ 2 * mollify k (F j) x ^ 2) volume :=
    ((hχ.continuous.pow 2).mul ((hFk j).continuous.pow 2)).integrable_of_hasCompactSupport
      (by simpa [pow_two, Pi.mul_def] using hc.mul_right.mul_right)
  have hPi (j : Fin n) : Integrable (fun x => coordinateDerivative f j x ^ 2) volume :=
    ((contDiff_coordinateDerivative hf (m := 0) (by norm_num) j).continuous.pow 2).integrable_of_hasCompactSupport
        (by simpa [pow_two, Pi.mul_def] using (hasCompactSupport_coordinateDerivative hfc j).mul_right)
  have hE := integrable_finsetSum Finset.univ (fun j _ => hEi j)
  have hA := integrable_finsetSum Finset.univ (fun j _ => hAi j)
  have hB := integrable_finsetSum Finset.univ (fun j _ => hBi j)
  have hP := integrable_finsetSum Finset.univ (fun j _ => hPi j)
  have hAbound : (∫ x, ∑ j, mollify k v x ^ 2 * coordinateDerivative χ j x ^ 2) ≤ ∑ j, A j := by
    rw [integral_finsetSum _ (fun j _ => hAi j)]
    exact Finset.sum_le_sum (fun j _ => by simpa only [mul_comm] using hAb j k)
  have hBbound : (∫ x, ∑ j, χ x ^ 2 * mollify k (F j) x ^ 2) ≤ ∑ j, B j := by
    rw [integral_finsetSum _ (fun j _ => hBi j)]
    exact Finset.sum_le_sum (fun j _ => hBb j k)
  have henergy := forced_caccioppoli_coordinate hχ hhk hFk hc (heq k)
  have hpoint (x : Space n) : (∑ j, coordinateDerivative f j x ^ 2) ≤
      2 * (∑ j, χ x ^ 2 * coordinateDerivative (mollify k v) j x ^ 2) +
        2 * (∑ j, mollify k v x ^ 2 * coordinateDerivative χ j x ^ 2) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    dsimp only [f]
    rw [coordinateDerivative_mul (hχ.differentiable (by norm_num) x)
      (hhk.differentiable (by norm_num) x)]
    nlinarith [sq_nonneg (χ x * coordinateDerivative (mollify k v) j x -
      mollify k v x * coordinateDerivative χ j x)]
  have hpbound := integral_mono hP ((hE.const_mul 2).add (hA.const_mul 2)) hpoint
  have hsplit := integral_add (hE.const_mul 2) (hA.const_mul 2)
  simp only [Pi.add_apply] at hpbound hsplit
  rw [hsplit, integral_const_mul, integral_const_mul] at hpbound
  have hsumBound : (∫ x, ∑ j, coordinateDerivative f j x ^ 2) ≤
      22 * (∑ j, A j) + 8 * (∑ j, B j) := by linarith
  apply le_trans (integral_mono (hPi i) hP ?_) hsumBound
  intro x
  exact Finset.single_le_sum (fun j _ => sq_nonneg (coordinateDerivative f j x)) (Finset.mem_univ i)

/-- The uniform derivative bound applies to the actual weighted L² annihilator,
without a pre-existing Sobolev derivative assumption. -/
theorem weighted_annihilator_localized_derivative_bound {φ χ : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (u : Lp ℝ 2 (potentialMeasure φ))
    (hu : ∀ g : Space n → ℝ, ContDiff ℝ 3 g → HasCompactSupport g →
      (∫ x, u x * weightedDiffusion φ g x ∂potentialMeasure φ) = 0)
    (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k : ℕ, ∀ i : Fin n,
      (∫ x, coordinateDerivative (fun y => χ y * mollify k (densityWeightedFunction φ u) y) i x ^ 2) ≤ M := by
  apply exists_uniform_derivative_sq_compact_mul_mollify (F := densityWeightedFlux φ u) hχ hc
    (fun K hK => memLp_densityWeightedFunction_restrict hφ.continuous u hK)
    (fun i K hK => memLp_densityWeightedFlux_restrict (hφ.of_le (by norm_num)) u hK i)
  intro k x
  exact laplacian_mollified_weighted_distribution hφ u hu
    (κ := mollifierKernel n k) ((mollifierKernel_contDiff k).of_le (by simp))
    (mollifierKernel_hasCompactSupport k) x

end KLS
end

#print axioms KLS.exists_uniform_derivative_sq_compact_mul_mollify
#print axioms KLS.weighted_annihilator_localized_derivative_bound

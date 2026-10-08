import KLS.C1WeightedDistribution
import KLS.WeightedMollification

/-!
# C¹ potential: C1WeightedMollification

This extension uses the actual diffusion and weighted L² representatives.
Only first derivatives of the source potential are required.
-/

open MeasureTheory InnerProductSpace Set Filter ContinuousLinearMap
open scoped ContDiff ENNReal Convolution Topology

noncomputable section
namespace KLS
variable {n : ℕ}

theorem weak_diffusion_reflected_kernel_C1 {φ κ : Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (u : Lp ℝ 2 (potentialMeasure φ))
    (hu : ∀ g : Space n → ℝ, ContDiff ℝ 3 g → HasCompactSupport g →
      (∫ x, u x * weightedDiffusion φ g x ∂potentialMeasure φ) = 0)
    (hκ : ContDiff ℝ 3 κ) (hc : HasCompactSupport κ) (a : Space n) :
    (∫ y, densityWeightedFunction φ u y * coordinateLaplacian κ (a - y)) =
      -(∑ i, ∫ y, densityWeightedFlux φ u i y * coordinateDerivative κ i (a - y)) := by
  have hg : ContDiff ℝ 3 (fun y => κ (a - y)) := hκ.comp (contDiff_const.sub contDiff_id)
  have hgc : HasCompactSupport (fun y => κ (a - y)) := hc.comp_homeomorph (Homeomorph.subLeft a)
  have he := weak_diffusion_unweighted_laplacian_C1 hφ u hu hg hgc
  have hlap (y : Space n) : coordinateLaplacian (fun y => κ (a - y)) y =
      coordinateLaplacian κ (a - y) := by
    unfold coordinateLaplacian
    exact Finset.sum_congr rfl (fun i _ => coordinateHessian_const_sub (hκ.of_le (by norm_num)) a y i i)
  have hi (i : Fin n) : Integrable (fun y => densityWeightedFlux φ u i y *
      coordinateDerivative κ i (a - y)) volume := by
    exact (hasCompactSupport_coordinateDerivative hc i).convolutionExists_right (lsmul ℝ ℝ)
      (locallyIntegrable_densityWeightedFlux (hφ.of_le (by norm_num)) u i)
      (contDiff_coordinateDerivative hκ (m := 0) (by norm_num) i).continuous a
  have hright : (∫ y, u y * Real.exp (-φ y) *
      inner ℝ (gradient φ y) (gradient (fun z => κ (a - z)) y)) =
      -(∑ i, ∫ y, densityWeightedFlux φ u i y * coordinateDerivative κ i (a - y)) := by
    rw [← integral_finsetSum _ (fun i _ => hi i), ← integral_neg]
    apply integral_congr_ae
    exact Eventually.of_forall fun y => by
      dsimp only
      rw [← sum_coordinateDerivative_mul, Finset.mul_sum]
      simp only [coordinateDerivative_const_sub (hκ.differentiable (by norm_num)),
        mul_neg, Finset.sum_neg_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      dsimp [densityWeightedFlux, densityWeightedFunction]
      ring
  rw [hright] at he
  convert he using 1
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by dsimp [densityWeightedFunction]; rw [hlap]

theorem laplacian_mollified_weighted_distribution_C1 {φ κ : Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (u : Lp ℝ 2 (potentialMeasure φ))
    (hu : ∀ g : Space n → ℝ, ContDiff ℝ 3 g → HasCompactSupport g →
      (∫ x, u x * weightedDiffusion φ g x ∂potentialMeasure φ) = 0)
    (hκ : ContDiff ℝ 3 κ) (hc : HasCompactSupport κ) (a : Space n) :
    coordinateLaplacian (scalarConvolution (densityWeightedFunction φ u) κ) a =
      -(∑ i, coordinateDerivative (scalarConvolution (densityWeightedFlux φ u i) κ) i a) := by
  have hloc := locallyIntegrable_densityWeightedFunction hφ.continuous u
  have hi (i : Fin n) : Integrable (fun y => densityWeightedFunction φ u y *
      coordinateHessian κ (a - y) i i) volume := by
    exact (hasCompactSupport_coordinateHessian hc i i).convolutionExists_right (lsmul ℝ ℝ)
      hloc (contDiff_coordinateHessian hκ (m := 0) (by norm_num) i i).continuous a
  have hleft : coordinateLaplacian (scalarConvolution (densityWeightedFunction φ u) κ) a =
      ∫ y, densityWeightedFunction φ u y * coordinateLaplacian κ (a - y) := by
    unfold coordinateLaplacian
    calc
      (∑ i, coordinateHessian (scalarConvolution (densityWeightedFunction φ u) κ) a i i) =
          ∑ i, ∫ y, densityWeightedFunction φ u y * coordinateHessian κ (a - y) i i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [coordinateHessian_scalarConvolution hloc (hκ.of_le (by norm_num)) hc]
        rfl
      _ = _ := by
        rw [← integral_finsetSum _ (fun i _ => hi i)]
        apply integral_congr_ae
        exact Eventually.of_forall fun y => by dsimp only; rw [Finset.mul_sum]
  rw [hleft, weak_diffusion_reflected_kernel_C1 hφ u hu hκ hc a]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [coordinateDerivative_scalarConvolution
    (locallyIntegrable_densityWeightedFlux (hφ.of_le (by norm_num)) u i)
    (hκ.of_le (by norm_num)) hc]
  rfl

end KLS
end

import KLS.ScalarMollification

/-!
# Mollification of the actual weighted distribution equation

For v = u exp(-φ), the weak diffusion equation becomes Δv = -div(v∇φ).
Both v and its drift flux are locally L². Convolution with a compact smooth
kernel therefore gives actual smooth functions satisfying the mollified
classical equation. No weak derivative of u is presumed in this step.
-/

open MeasureTheory InnerProductSpace Set Filter ContinuousLinearMap
open scoped ContDiff ENNReal Convolution Topology

noncomputable section
namespace KLS

variable {n : ℕ}

lemma memLp_mul_continuous_on_compact {f g : Space n → ℝ}
    {K : Set (Space n)} (hK : IsCompact K) (hf : MemLp f 2 (volume.restrict K))
    (hg : Continuous g) : MemLp (fun x => f x * g x) 2 (volume.restrict K) := by
  obtain ⟨C, hC⟩ := hK.bddAbove_image hg.norm.continuousOn
  have hgtop : MemLp g ⊤ (volume.restrict K) :=
    memLp_top_of_bound hg.aestronglyMeasurable C
      ((ae_restrict_mem hK.measurableSet).mono (fun x hx => hC (mem_image_of_mem _ hx)))
  exact hf.mul hgtop

lemma locallyIntegrable_of_memLp_two_on_compacts {f : Space n → ℝ}
    (hf : ∀ K : Set (Space n), IsCompact K → MemLp f 2 (volume.restrict K)) :
    LocallyIntegrable f volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  exact MeasureTheory.MemLp.integrable (q := 2) (by norm_num) (hf K hK)

/-- The actual Lebesgue density multiplied by the weighted L² representative. -/
def densityWeightedFunction (φ : Space n → ℝ) (u : Lp ℝ 2 (potentialMeasure φ)) : Space n → ℝ :=
  fun x => u x * Real.exp (-φ x)

/-- The actual flux in the transformed divergence equation. -/
def densityWeightedFlux (φ : Space n → ℝ) (u : Lp ℝ 2 (potentialMeasure φ))
    (i : Fin n) : Space n → ℝ :=
  fun x => densityWeightedFunction φ u x * coordinateDerivative φ i x

theorem memLp_densityWeightedFunction_restrict {φ : Space n → ℝ} (hφ : Continuous φ)
    (u : Lp ℝ 2 (potentialMeasure φ)) {K : Set (Space n)} (hK : IsCompact K) :
    MemLp (densityWeightedFunction φ u) 2 (volume.restrict K) :=
  memLp_mul_continuous_on_compact hK
    (KLS.MemLp.restrict_volume_of_potentialMeasure (Lp.memLp u) hφ hK)
    (Real.continuous_exp.comp hφ.neg)

theorem memLp_densityWeightedFlux_restrict {φ : Space n → ℝ} (hφ : ContDiff ℝ 1 φ)
    (u : Lp ℝ 2 (potentialMeasure φ)) {K : Set (Space n)} (hK : IsCompact K) (i : Fin n) :
    MemLp (densityWeightedFlux φ u i) 2 (volume.restrict K) :=
  memLp_mul_continuous_on_compact hK (memLp_densityWeightedFunction_restrict hφ.continuous u hK)
    (contDiff_coordinateDerivative hφ (m := 0) (by norm_num) i).continuous

lemma locallyIntegrable_densityWeightedFunction {φ : Space n → ℝ} (hφ : Continuous φ)
    (u : Lp ℝ 2 (potentialMeasure φ)) : LocallyIntegrable (densityWeightedFunction φ u) volume :=
  locallyIntegrable_of_memLp_two_on_compacts (fun _ hK =>
    memLp_densityWeightedFunction_restrict hφ u hK)

lemma locallyIntegrable_densityWeightedFlux {φ : Space n → ℝ} (hφ : ContDiff ℝ 1 φ)
    (u : Lp ℝ 2 (potentialMeasure φ)) (i : Fin n) :
    LocallyIntegrable (densityWeightedFlux φ u i) volume :=
  locallyIntegrable_of_memLp_two_on_compacts (fun _ hK =>
    memLp_densityWeightedFlux_restrict hφ u hK i)

lemma coordinateHessian_scalarConvolution {f κ : Space n → ℝ}
    (hf : LocallyIntegrable f volume) (hκ : ContDiff ℝ 2 κ)
    (hc : HasCompactSupport κ) (i j : Fin n) (x : Space n) :
    coordinateHessian (scalarConvolution f κ) x i j =
      scalarConvolution f (fun y => coordinateHessian κ y i j) x := by
  have hd : coordinateDerivative (scalarConvolution f κ) j =
      scalarConvolution f (coordinateDerivative κ j) :=
    funext (coordinateDerivative_scalarConvolution hf (hκ.of_le (by norm_num)) hc j)
  unfold coordinateHessian
  rw [hd, coordinateDerivative_scalarConvolution hf
    (contDiff_coordinateDerivative hκ (m := 1) (by norm_num) j)
    (hasCompactSupport_coordinateDerivative hc j)]

/-- The transformed distribution identity evaluated at a reflected kernel. -/
theorem weak_diffusion_reflected_kernel {φ κ : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (u : Lp ℝ 2 (potentialMeasure φ))
    (hu : ∀ g : Space n → ℝ, ContDiff ℝ 3 g → HasCompactSupport g →
      (∫ x, u x * weightedDiffusion φ g x ∂potentialMeasure φ) = 0)
    (hκ : ContDiff ℝ 3 κ) (hc : HasCompactSupport κ) (a : Space n) :
    (∫ y, densityWeightedFunction φ u y * coordinateLaplacian κ (a - y)) =
      -(∑ i, ∫ y, densityWeightedFlux φ u i y * coordinateDerivative κ i (a - y)) := by
  have hg : ContDiff ℝ 3 (fun y => κ (a - y)) := hκ.comp (contDiff_const.sub contDiff_id)
  have hgc : HasCompactSupport (fun y => κ (a - y)) := hc.comp_homeomorph (Homeomorph.subLeft a)
  have he := weak_diffusion_unweighted_laplacian hφ u hu hg hgc
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

/-- Mollification gives an actual classical Laplace-divergence equation. -/
theorem laplacian_mollified_weighted_distribution {φ κ : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (u : Lp ℝ 2 (potentialMeasure φ))
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

  rw [hleft, weak_diffusion_reflected_kernel hφ u hu hκ hc a]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [coordinateDerivative_scalarConvolution
    (locallyIntegrable_densityWeightedFlux (hφ.of_le (by norm_num)) u i)
    (hκ.of_le (by norm_num)) hc]
  rfl

end KLS
end

#print axioms KLS.memLp_densityWeightedFunction_restrict
#print axioms KLS.memLp_densityWeightedFlux_restrict
#print axioms KLS.weak_diffusion_reflected_kernel
#print axioms KLS.laplacian_mollified_weighted_distribution

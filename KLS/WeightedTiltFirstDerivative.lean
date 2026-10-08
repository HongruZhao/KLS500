import KLS.WeightedTiltSmooth
import KLS.WeightedTiltIntegration
import KLS.TiltCumulantLowOrders

/-! The first Taylor identity for the genuine weighted L² diffusion domain.
Smoothness of each actual gradient-coordinate tilt is derived from its L²
bound. The derivative is obtained from the already proved normalized tilted
integration identity, without assuming a Taylor identity or growth bound. -/

open MeasureTheory InnerProductSpace Matrix
open scoped ContDiff RealInnerProductSpace Topology BigOperators

noncomputable section
namespace KLS
variable {n : ℕ}

theorem memLp_gradient_of_integrable_sq {φ f : Space n → ℝ}
    (hf : ContDiff ℝ 1 f)
    (hF : Integrable (fun x => ‖gradient f x‖ ^ 2) (potentialMeasure φ)) :
    MemLp (gradient f) 2 (potentialMeasure φ) :=
  (memLp_two_iff_integrable_sq_norm
    (continuous_gradient_of_contDiff hf).aestronglyMeasurable).mpr hF

theorem contDiff_exponentialTilt_gradient_coordinate {φ f : Space n → ℝ} {κ : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ y (v : Fin n → ℝ),
      κ * (v ⬝ᵥ v) ≤ v ⬝ᵥ (coordinateHessian φ y *ᵥ v))
    (hf : ContDiff ℝ 1 f)
    (hF : Integrable (fun x => ‖gradient f x‖ ^ 2) (potentialMeasure φ)) (i : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun z => ∫ x, gradient f x i ∂exponentialTilt (potentialMeasure φ) z) := by
  apply contDiff_exponentialTilt_average_of_weighted_memLp hφ hκ hlower
  exact (EuclideanSpace.proj i : Space n →L[ℝ] ℝ).comp_memLp'
    (memLp_gradient_of_integrable_sq hf hF)

/-- Literal Fréchet form of BKL (49), throughout the actual L² domain. -/
theorem hasFDerivAt_weightedDiffusion_exponentialTilt_zero
    {φ f : Space n → ℝ} {κ : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ y (v : Fin n → ℝ),
      κ * (v ⬝ᵥ v) ≤ v ⬝ᵥ (coordinateHessian φ y *ᵥ v))
    (hf : ContDiff ℝ 2 f)
    (hL : MemLp (weightedDiffusion φ f) 2 (potentialMeasure φ))
    (hF : Integrable (fun x => ‖gradient f x‖ ^ 2) (potentialMeasure φ)) :
    HasFDerivAt
      (fun z => ∫ x, -weightedDiffusion φ f x ∂exponentialTilt (potentialMeasure φ) z)
      (innerSL ℝ (∫ x, gradient f x ∂potentialMeasure φ)) 0 := by
  have hi (i : Fin n) :=
    contDiff_exponentialTilt_gradient_coordinate hφ hκ hlower (hf.of_le (by norm_num)) hF i
  have hid (z : Space n) :
      (∫ x, -weightedDiffusion φ f x ∂exponentialTilt (potentialMeasure φ) z) =
        ∑ i, z i * (∫ x, gradient f x i ∂exponentialTilt (potentialMeasure φ) z) := by
    rw [weightedDiffusion_exponentialTilt_identity hφ hκ hlower hf hL hF]
    rw [real_inner_comm, inner_eq_coordinate_sum]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    exact ((EuclideanSpace.proj i : Space n →L[ℝ] ℝ).integral_comp_comm
      (integrable_gradient_exponentialTilt_of_L2 hφ hκ hlower (hf.of_le (by norm_num)) hF z)).symm
  have hsum := HasFDerivAt.sum (u := Finset.univ) (x := (0 : Space n)) (fun i _ =>
    (EuclideanSpace.proj i : Space n →L[ℝ] ℝ).hasFDerivAt.mul
      ((hi i).differentiable (by simp)).differentiableAt.hasFDerivAt)
  simp only [EuclideanSpace.coe_proj, PiLp.zero_apply, zero_smul, zero_add] at hsum
  convert hsum using 1
  · funext z
    simpa only [Finset.sum_apply, Pi.mul_apply] using hid z
  · ext v
    simp only [_root_.sum_apply, _root_.smul_apply, smul_eq_mul, EuclideanSpace.coe_proj,
      innerSL_apply_apply]
    rw [inner_eq_coordinate_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hgrad : Integrable (gradient f) (potentialMeasure φ) :=
      (memLp_gradient_of_integrable_sq (hf.of_le (by norm_num)) hF).integrable (by norm_num)
    have h0 : exponentialTilt (potentialMeasure φ) 0 = potentialMeasure φ := by
      simp [exponentialTilt]
    rw [h0]
    have hcoord := (EuclideanSpace.proj i : Space n →L[ℝ] ℝ).integral_comp_comm hgrad
    change (∫ x, gradient f x i ∂potentialMeasure φ) =
      (∫ x, gradient f x ∂potentialMeasure φ) i at hcoord
    rw [← hcoord]
    ring

end KLS
end

#print axioms KLS.memLp_gradient_of_integrable_sq
#print axioms KLS.contDiff_exponentialTilt_gradient_coordinate
#print axioms KLS.hasFDerivAt_weightedDiffusion_exponentialTilt_zero

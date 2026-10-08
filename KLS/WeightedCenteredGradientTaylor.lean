import KLS.WeightedTiltTaylorLinearity
import KLS.WeightedSuccessorDomain

/-! The literal centered gradient and its genuine Taylor tensor. Centering
does not change positive-degree coefficients, so the full mixed diffusion
identity continues to hold with the actual centered gradient. -/

open MeasureTheory InnerProductSpace Matrix
open scoped ContDiff RealInnerProductSpace Topology BigOperators

noncomputable section
namespace KLS
variable {n : ℕ}

def weightedCenteredGradientCoordinate (φ f : Space n → ℝ) (j : Fin n) (x : Space n) : ℝ :=
  coordinateDerivative f j x - ∫ y, coordinateDerivative f j y ∂potentialMeasure φ

def exponentialTiltCenteredGradientTaylor (φ f : Space n → ℝ) (d : ℕ)
    (a : Fin (d + 1) → Fin n) : ℝ :=
  exponentialTiltCoordinateTaylor φ (weightedCenteredGradientCoordinate φ f (a (Fin.last d))) d
    (fun j => a j.castSucc)

theorem weightedH1_memLp_coordinateDerivative_of_representative {φ f : Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (U : WeightedCenteredH1 φ) (hf : ContDiff ℝ 1 f)
    (hv : f =ᵐ[volume] (weightedH1Value φ U : Space n → ℝ)) (j : Fin n) :
    MemLp (coordinateDerivative f j) 2 (potentialMeasure φ) := by
  have hd : coordinateDerivative f j =ᵐ[potentialMeasure φ]
      (weightedH1Derivative φ j U : Space n → ℝ) :=
    (withDensity_absolutelyContinuous _ _).ae_eq
      (weightedH1_coordinateDerivative_of_representative hφ U hf hv j)
  exact (memLp_congr_ae hd).mpr (Lp.memLp _)

theorem weightedH1_integrable_gradient_norm_sq_of_representative {φ f : Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (U : WeightedCenteredH1 φ) (hf : ContDiff ℝ 1 f)
    (hv : f =ᵐ[volume] (weightedH1Value φ U : Space n → ℝ)) :
    Integrable (fun x => ‖gradient f x‖ ^ 2) (potentialMeasure φ) :=
  integrable_gradient_norm_sq_of_energy_lt_top
    (energy_lt_top_of_memLp_coordinateDerivative
      (weightedH1_memLp_coordinateDerivative_of_representative hφ U hf hv))

variable {φ : Space n → ℝ} {κ : ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))

include hφ hκ hlower

theorem exponentialTiltCenteredGradientTaylor_eq {f : Space n → ℝ}
    (hf : ContDiff ℝ 1 f)
    (hF : Integrable (fun x => ‖gradient f x‖ ^ 2) (potentialMeasure φ))
    {d : ℕ} (hd : d ≠ 0) (a : Fin (d + 1) → Fin n) :
    exponentialTiltCenteredGradientTaylor φ f d a = exponentialTiltGradientTaylor φ f d a := by
  have hm : MemLp (coordinateDerivative f (a (Fin.last d))) 2 (potentialMeasure φ) := by
    convert
      (EuclideanSpace.proj (a (Fin.last d)) : Space n →L[ℝ] ℝ).comp_memLp'
        (memLp_gradient_of_integrable_sq hf hF) using 1
    funext x
    exact coordinateDerivative_eq_gradient _ _ _
  unfold exponentialTiltCenteredGradientTaylor weightedCenteredGradientCoordinate
  rw [exponentialTiltCoordinateTaylor_sub_const hφ hκ hlower hm _ hd]
  unfold exponentialTiltGradientTaylor
  congr 1
  funext x
  exact coordinateDerivative_eq_gradient _ _ _

/-- The full centered version of BKL (50) at every positive Taylor degree. -/
theorem weightedDiffusion_exponentialTilt_centered_taylor_tensor {f : Space n → ℝ}
    (hf : ContDiff ℝ 2 f)
    (hL : MemLp (weightedDiffusion φ f) 2 (potentialMeasure φ))
    (hF : Integrable (fun x => ‖gradient f x‖ ^ 2) (potentialMeasure φ))
    {d : ℕ} (hd : d ≠ 0) (a : Fin (d + 1) → Fin n) :
    exponentialTiltCoordinateTaylor φ (-weightedDiffusion φ f) (d + 1) a =
      (∑ σ : Equiv.Perm (Fin (d + 1)),
        exponentialTiltCenteredGradientTaylor φ f d (a ∘ σ)) / (d + 1).factorial := by
  simp_rw [exponentialTiltCenteredGradientTaylor_eq hφ hκ hlower (hf.of_le (by norm_num)) hF hd]
  exact weightedDiffusion_exponentialTilt_taylor_tensor hφ hκ hlower hf hL hF d a

end KLS
end

#print axioms KLS.weightedH1_integrable_gradient_norm_sq_of_representative
#print axioms KLS.exponentialTiltCenteredGradientTaylor_eq
#print axioms KLS.weightedDiffusion_exponentialTilt_centered_taylor_tensor

import KLS.WeightedTiltTaylorTensor

/-! Linearity and insensitivity to constants of the actual normalized tilted
Taylor coefficients. Every integrability and smoothness condition is derived
from weighted L2 membership under the genuine uniformly convex measure. -/

open MeasureTheory InnerProductSpace Matrix
open scoped ContDiff RealInnerProductSpace Topology BigOperators

noncomputable section
namespace KLS
variable {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))

include hφ hκ hlower

omit [IsProbabilityMeasure (potentialMeasure φ)] in
theorem integrable_exponentialTilt_of_weighted_memLp {f : Space n → ℝ}
    (hf : MemLp f 2 (potentialMeasure φ)) (z : Space n) :
    Integrable f (exponentialTilt (potentialMeasure φ) z) := by
  change Integrable f ((potentialMeasure φ).tilted (fun x => inner ℝ z x))
  rw [integrable_tilted_iff (integrable_exp_inner_potentialMeasure hφ hκ hlower z)]
  convert (memLp_exp_inner_potentialMeasure hφ hκ hlower z).integrable_mul hf using 1

theorem exponentialTiltCoordinateTaylor_const_mul {f : Space n → ℝ}
    (hf : MemLp f 2 (potentialMeasure φ)) (c : ℝ) (d : ℕ) (a : Fin d → Fin n) :
    exponentialTiltCoordinateTaylor φ (fun x => c * f x) d a =
      c * exponentialTiltCoordinateTaylor φ f d a := by
  have hs := contDiff_exponentialTilt_average_of_weighted_memLp hφ hκ hlower hf
  have he : (fun z => ∫ x, c * f x ∂exponentialTilt (potentialMeasure φ) z) =
      c • (fun z => ∫ x, f x ∂exponentialTilt (potentialMeasure φ) z) := by
    funext z
    simp only [integral_const_mul, Pi.smul_apply, smul_eq_mul]
  unfold exponentialTiltCoordinateTaylor exponentialTiltTaylorCoefficient
  rw [he, iteratedFDeriv_const_smul_apply ((hs.of_le (by simp)).contDiffAt)]
  simp only [_root_.smul_apply, smul_eq_mul]
  ring

theorem exponentialTiltCoordinateTaylor_sub {f g : Space n → ℝ}
    (hf : MemLp f 2 (potentialMeasure φ)) (hg : MemLp g 2 (potentialMeasure φ))
    (d : ℕ) (a : Fin d → Fin n) :
    exponentialTiltCoordinateTaylor φ (fun x => f x - g x) d a =
      exponentialTiltCoordinateTaylor φ f d a - exponentialTiltCoordinateTaylor φ g d a := by
  have hsf := contDiff_exponentialTilt_average_of_weighted_memLp hφ hκ hlower hf
  have hsg := contDiff_exponentialTilt_average_of_weighted_memLp hφ hκ hlower hg
  have he : (fun z => ∫ x, f x - g x ∂exponentialTilt (potentialMeasure φ) z) =
      (fun z => ∫ x, f x ∂exponentialTilt (potentialMeasure φ) z) -
        (fun z => ∫ x, g x ∂exponentialTilt (potentialMeasure φ) z) := by
    funext z
    exact integral_sub (integrable_exponentialTilt_of_weighted_memLp hφ hκ hlower hf z)
      (integrable_exponentialTilt_of_weighted_memLp hφ hκ hlower hg z)
  unfold exponentialTiltCoordinateTaylor exponentialTiltTaylorCoefficient
  rw [he, iteratedFDeriv_sub_apply ((hsf.of_le (by simp)).contDiffAt)
    ((hsg.of_le (by simp)).contDiffAt)]
  simp only [_root_.sub_apply]
  ring

theorem exponentialTiltCoordinateTaylor_const (c : ℝ) {d : ℕ} (hd : d ≠ 0)
    (a : Fin d → Fin n) : exponentialTiltCoordinateTaylor φ (fun _ => c) d a = 0 := by
  have he : (fun z => ∫ _x : Space n, c ∂exponentialTilt (potentialMeasure φ) z) = fun _ => c := by
    funext z
    let := exponentialTilt_potentialMeasure_isProbability hφ hκ hlower z
    simp
  unfold exponentialTiltCoordinateTaylor exponentialTiltTaylorCoefficient
  rw [he, iteratedFDeriv_const_of_ne hd]
  simp

theorem exponentialTiltCoordinateTaylor_sub_const {f : Space n → ℝ}
    (hf : MemLp f 2 (potentialMeasure φ)) (c : ℝ) {d : ℕ} (hd : d ≠ 0)
    (a : Fin d → Fin n) :
    exponentialTiltCoordinateTaylor φ (fun x => f x - c) d a =
      exponentialTiltCoordinateTaylor φ f d a := by
  rw [exponentialTiltCoordinateTaylor_sub hφ hκ hlower hf (memLp_const c),
    exponentialTiltCoordinateTaylor_const hφ hκ hlower c hd, sub_zero]

end KLS
end

#print axioms KLS.integrable_exponentialTilt_of_weighted_memLp
#print axioms KLS.exponentialTiltCoordinateTaylor_const_mul
#print axioms KLS.exponentialTiltCoordinateTaylor_sub
#print axioms KLS.exponentialTiltCoordinateTaylor_sub_const

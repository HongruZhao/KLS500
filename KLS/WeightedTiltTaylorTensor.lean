import KLS.WeightedTiltSymmetrizedTaylor

/-! Literal coordinate Taylor tensors, placing all Taylor indices before
the original gradient index, and the full permutation identity of BKL (50). -/
open MeasureTheory InnerProductSpace Matrix
open scoped ContDiff RealInnerProductSpace Topology BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

/-- Actual d-th tilted Taylor tensor entry, including the Taylor factorial. -/
def exponentialTiltCoordinateTaylor (φ f : Space n → ℝ) (d : ℕ)
    (a : Fin d → Fin n) : ℝ :=
  exponentialTiltTaylorCoefficient φ f d (fun j => EuclideanSpace.single (a j) 1)

/-- Original gradient index last, after the d Taylor indices. -/
def exponentialTiltGradientTaylor (φ f : Space n → ℝ) (d : ℕ)
    (a : Fin (d + 1) → Fin n) : ℝ :=
  exponentialTiltCoordinateTaylor φ (fun x => gradient f x (a (Fin.last d))) d
    (fun j => a j.castSucc)

/-- Literal coordinate tensor equality T_(d+1)(-Lf) = S_(d+1) T_d(grad f),
with actual normalized tilt derivatives and paper-order tensor slots. -/
theorem weightedDiffusion_exponentialTilt_taylor_tensor
    {φ f : Space n → ℝ} {κ : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ y (v : Fin n → ℝ),
      κ * (v ⬝ᵥ v) ≤ v ⬝ᵥ (coordinateHessian φ y *ᵥ v))
    (hf : ContDiff ℝ 2 f)
    (hL : MemLp (weightedDiffusion φ f) 2 (potentialMeasure φ))
    (hF : Integrable (fun x => ‖gradient f x‖ ^ 2) (potentialMeasure φ))
    (d : ℕ) (a : Fin (d + 1) → Fin n) :
    exponentialTiltCoordinateTaylor φ (-weightedDiffusion φ f) (d + 1) a =
      (∑ σ : Equiv.Perm (Fin (d + 1)),
        exponentialTiltGradientTaylor φ f d (a ∘ σ)) / (d + 1).factorial := by
  simpa only [exponentialTiltCoordinateTaylor, exponentialTiltGradientTaylor,
    Function.comp_apply, EuclideanSpace.inner_single_left, map_one, one_mul] using
    weightedDiffusion_exponentialTilt_symmetrized_taylor hφ hκ hlower hf hL hF d
      (fun j => EuclideanSpace.single (a j) 1)

/-- Every original tensor component satisfies the same equality, with its
original component index left fixed by the Taylor/gradient symmetrizer. -/
theorem weightedDiffusion_exponentialTilt_family_taylor_tensor
    {ι : Type*} {φ : Space n → ℝ} {f : ι → Space n → ℝ} {κ : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ y (v : Fin n → ℝ),
      κ * (v ⬝ᵥ v) ≤ v ⬝ᵥ (coordinateHessian φ y *ᵥ v))
    (hf : ∀ i, ContDiff ℝ 2 (f i))
    (hL : ∀ i, MemLp (weightedDiffusion φ (f i)) 2 (potentialMeasure φ))
    (hF : ∀ i, Integrable (fun x => ‖gradient (f i) x‖ ^ 2) (potentialMeasure φ))
    (d : ℕ) (i : ι) (a : Fin (d + 1) → Fin n) :
    exponentialTiltCoordinateTaylor φ (-weightedDiffusion φ (f i)) (d + 1) a =
      (∑ σ : Equiv.Perm (Fin (d + 1)),
        exponentialTiltGradientTaylor φ (f i) d (a ∘ σ)) / (d + 1).factorial :=
  weightedDiffusion_exponentialTilt_taylor_tensor hφ hκ hlower (hf i) (hL i) (hF i) d a

end KLS
end
#print axioms KLS.exponentialTiltCoordinateTaylor
#print axioms KLS.exponentialTiltGradientTaylor
#print axioms KLS.weightedDiffusion_exponentialTilt_taylor_tensor
#print axioms KLS.weightedDiffusion_exponentialTilt_family_taylor_tensor

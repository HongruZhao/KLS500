import KLS.WeightedL2TaylorTensor
import KLS.WeightedTensorPermutationAction
import KLS.FiniteIsometryAverageAlgebra

/-! Actual permutations of the real coordinate Taylor tensor. Taylor-index
symmetry comes from genuine mixed-derivative symmetry. Original-component
permutations and their finite averages commute with the actual Taylor map. -/

open MeasureTheory Matrix
open scoped ContDiff RealInnerProductSpace Topology BigOperators
noncomputable section
namespace KLS

def finiteScalarReindex {ι ι' : Type*} [Fintype ι] [Fintype ι'] (e : ι ≃ ι') :
    EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι' :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e

@[simp] theorem finiteScalarReindex_apply {ι ι' : Type*} [Fintype ι] [Fintype ι']
    (e : ι ≃ ι') (T : EuclideanSpace ℝ ι) (i : ι') :
    finiteScalarReindex e T i = T (e.symm i) := rfl

def finiteScalarReindexHom (ι : Type*) [Fintype ι] :
    Equiv.Perm ι →* (EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) where
  toFun := finiteScalarReindex
  map_one' := by ext T i; rfl
  map_mul' e f := by ext T i; rfl

def tensorTailPermutationHom (A ι : Type*) : Equiv.Perm ι →* Equiv.Perm (A × ι) where
  toFun e := Equiv.prodCongr (Equiv.refl A) e
  map_one' := by ext x <;> rfl
  map_mul' e f := by ext x <;> rfl

variable {n : ℕ} {φ : Space n → ℝ}

theorem weightedL2TaylorTensor_reindex (d : ℕ) {ι ι' : Type*} [Fintype ι] [Fintype ι']
    (e : ι ≃ ι') (g : CenteredL2.Family (potentialMeasure φ) ι) :
    weightedL2TaylorTensor φ d (finiteL2Reindex e g) =
      finiteScalarReindex (Equiv.prodCongr (Equiv.refl (Fin d → Fin n)) e)
        (weightedL2TaylorTensor φ d g) := by
  apply PiLp.ext
  rintro ⟨a, i⟩
  rfl

def weightedTaylorTailAction (n d : ℕ) {G ι : Type*} [Group G] [Fintype ι]
    (ρ : G →* Equiv.Perm ι) : G →*
      (EuclideanSpace ℝ ((Fin d → Fin n) × ι) ≃ₗᵢ[ℝ] EuclideanSpace ℝ ((Fin d → Fin n) × ι)) :=
  (finiteScalarReindexHom _).comp ((tensorTailPermutationHom (Fin d → Fin n) ι).comp ρ)

variable {κ : ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))

include hφ hκ hlower

/-- The actual Taylor map intertwines the literal original-index averages. -/
theorem weightedL2TaylorTensor_average (d : ℕ) {G ι : Type*} [Group G] [Fintype G] [Fintype ι]
    (ρ : G →* Equiv.Perm ι) (g : CenteredL2.Family (potentialMeasure φ) ι) :
    weightedL2TaylorTensor φ d (finiteIsometryAverage
      ((finiteL2ReindexHom (potentialMeasure φ) ι).comp ρ) g) =
        finiteIsometryAverage (weightedTaylorTailAction n d ρ) (weightedL2TaylorTensor φ d g) := by
  change weightedL2TaylorLinearMap hφ hκ hlower d ι
    ((Fintype.card G : ℝ)⁻¹ • ∑ σ : G, ((finiteL2ReindexHom (potentialMeasure φ) ι).comp ρ) σ g) =
      (Fintype.card G : ℝ)⁻¹ • ∑ σ : G, weightedTaylorTailAction n d ρ σ (weightedL2TaylorTensor φ d g)
  rw [map_smul, map_sum]
  congr 1

theorem exponentialTiltCoordinateTaylor_comp_perm {f : Space n → ℝ}
    (hf : MemLp f 2 (potentialMeasure φ)) (d : ℕ) (a : Fin d → Fin n)
    (σ : Equiv.Perm (Fin d)) :
    exponentialTiltCoordinateTaylor φ f d (a ∘ σ) = exponentialTiltCoordinateTaylor φ f d a := by
  have hs := contDiff_exponentialTilt_average_of_weighted_memLp hφ hκ hlower hf
  unfold exponentialTiltCoordinateTaylor exponentialTiltTaylorCoefficient
  congr 1
  exact smooth_iteratedFDeriv_comp_perm hs (fun j => EuclideanSpace.single (a j) 1) σ 0

/-- Taylor-index symmetry is proved for the actual coordinate coefficients,
not imposed as a tensor-symmetry premise. -/
theorem weightedL2TaylorTensor_taylor_symmetric (d : ℕ) {ι : Type*} [Fintype ι]
    (g : CenteredL2.Family (potentialMeasure φ) ι) (σ : Equiv.Perm (Fin d)) :
    ((finiteScalarReindexHom ((Fin d → Fin n) × ι)).comp
      (tensorCoordinatePermHom (Fin n) ι d)) σ (weightedL2TaylorTensor φ d g) =
        weightedL2TaylorTensor φ d g := by
  apply PiLp.ext
  rintro ⟨a, i⟩
  change exponentialTiltCoordinateTaylor φ (g i) d (a ∘ σ) =
    exponentialTiltCoordinateTaylor φ (g i) d a
  exact exponentialTiltCoordinateTaylor_comp_perm hφ hκ hlower (Lp.memLp _) d a σ

end KLS
end

#print axioms KLS.weightedL2TaylorTensor_reindex
#print axioms KLS.weightedL2TaylorTensor_average
#print axioms KLS.weightedL2TaylorTensor_taylor_symmetric

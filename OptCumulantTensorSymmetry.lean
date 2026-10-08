import OptSymmetricTensorSpace
import KLS.AdaptiveCumulantEnergy
import KLS.DirectionalWordSymmetry

open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped Topology BigOperators Matrix.Norms.Elementwise
noncomputable section
namespace KLS.TensorEnergy
variable {n r : ℕ}

def tensorTailPermutation (σ : Equiv.Perm (Fin r)) : Equiv.Perm (Fin (r+1)) where
  toFun := Fin.cases 0 (fun i => (σ i).succ)
  invFun := Fin.cases 0 (fun i => (σ.symm i).succ)
  left_inv := by intro i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
  right_inv := by intro i; refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem tensorMatrix_preserves_symmetry (H : Matrix (Fin n) (Fin n) ℝ)
    (T : (Fin r → Fin n) → ℝ)
    (hT : ∀ (σ : Equiv.Perm (Fin r)) a, T (a ∘ σ) = T a) :
    ∀ (σ : Equiv.Perm (Fin r)) a,
      (tensorMatrix H *ᵥ T) (a ∘ σ) = (tensorMatrix H *ᵥ T) a := by
  intro σ a
  change (∑ b, tensorMatrix H (a ∘ σ) b * T b) = ∑ b, tensorMatrix H a b * T b
  calc
    _ = ∑ b, tensorMatrix H (a ∘ σ) (b ∘ σ) * T (b ∘ σ) :=
      ((coordinateReindexEquiv (n := n) σ).sum_comp
        (fun b => tensorMatrix H (a ∘ σ) b * T b)).symm
    _ = _ := by simp only [tensorMatrix_reindex, hT]

end KLS.TensorEnergy
namespace KLS.AdaptiveLocalization
open KLS.TensorEnergy
variable {n r : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

theorem coordinateCumulantTensor_symmetric (hμ : IsCompact μ.support)
    (u : Space n) (z : Fin (n+n*n) → ℝ) (σ : Equiv.Perm (Fin r)) (a : Fin r → Fin n) :
    coordinateCumulantTensor μ r u z (a ∘ σ) = coordinateCumulantTensor μ r u z a := by
  let p := decodeState z
  have := law_isProbability hμ p.1 p.2
  have hc : IsCompact (law μ p.1 p.2).support := by rwa [support_law hμ]
  have hh := smooth_iteratedFDeriv_comp_perm (contDiff_tiltLogLaplace hc)
    (cumulantSliceDirections u a) (tensorTailPermutation σ) 0
  have he : cumulantSliceDirections u a ∘ tensorTailPermutation σ = cumulantSliceDirections u (a ∘ σ) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [tensorTailPermutation, cumulantSliceDirections]
  rw [he] at hh
  exact hh

theorem whitenedCumulantTensor_symmetric (hμ : IsCompact μ.support)
    (u : Space n) (z : Fin (n+n*n) → ℝ) (σ : Equiv.Perm (Fin r)) (a : Fin r → Fin n) :
    whitenedCumulantTensor μ r u z (a ∘ σ) = whitenedCumulantTensor μ r u z a :=
  tensorMatrix_preserves_symmetry _ _ (coordinateCumulantTensor_symmetric hμ u z) σ a

end KLS.AdaptiveLocalization
end

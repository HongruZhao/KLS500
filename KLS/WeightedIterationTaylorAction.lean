import KLS.WeightedTaylorPermutation
import KLS.WeightedIterationTaylorRecursion

/-! The actual L2-family Corollary 3.7 as an equality of finite real tensors
and literal permutation averages. No coordinate symmetry premise is added. -/

open MeasureTheory Matrix
open scoped ContDiff RealInnerProductSpace Topology BigOperators
noncomputable section
namespace KLS

def mergeTaylorGradientEquiv (n d : ℕ) (ι : Type*) :
    ((Fin d → Fin n) × (Fin n × ι)) ≃ ((Fin (d + 1) → Fin n) × ι) :=
  (Equiv.prodAssoc (Fin d → Fin n) (Fin n) ι).symm.trans
    (Equiv.prodCongr ((Equiv.prodComm (Fin d → Fin n) (Fin n)).trans
      (Fin.snocEquiv (fun _ : Fin (d + 1) => Fin n))) (Equiv.refl ι))

@[simp] theorem mergeTaylorGradientEquiv_symm_apply (n d : ℕ) (ι : Type*)
    (a : Fin (d + 1) → Fin n) (i : ι) :
    (mergeTaylorGradientEquiv n d ι).symm (a, i) = (Fin.init a, (a (Fin.last d), i)) := rfl

def weightedL2GradientTaylor {n : ℕ} (φ : Space n → ℝ) (d : ℕ)
    {ι : Type*} [Fintype ι] (g : CenteredL2.Family (potentialMeasure φ) (Fin n × ι)) :
    EuclideanSpace ℝ ((Fin (d + 1) → Fin n) × ι) :=
  finiteScalarReindex (mergeTaylorGradientEquiv n d ι) (weightedL2TaylorTensor φ d g)

@[simp] theorem weightedL2GradientTaylor_apply {n : ℕ} (φ : Space n → ℝ) (d : ℕ)
    {ι : Type*} [Fintype ι] (g : CenteredL2.Family (potentialMeasure φ) (Fin n × ι))
    (a : Fin (d + 1) → Fin n) (i : ι) :
    weightedL2GradientTaylor φ d g (a, i) =
      exponentialTiltCoordinateTaylor φ (g (a (Fin.last d), i)) d (Fin.init a) := rfl

def realCoordinatePermutationAction (n q : ℕ) (ι : Type*) [Fintype ι] :
    Equiv.Perm (Fin q) →*
      (EuclideanSpace ℝ ((Fin q → Fin n) × ι) ≃ₗᵢ[ℝ] EuclideanSpace ℝ ((Fin q → Fin n) × ι)) :=
  (finiteScalarReindexHom _).comp (tensorCoordinatePermHom (Fin n) ι q)

theorem realCoordinatePermutationAverage_apply (n q : ℕ) (ι : Type*) [Fintype ι]
    (T : EuclideanSpace ℝ ((Fin q → Fin n) × ι)) (a : Fin q → Fin n) (i : ι) :
    finiteIsometryAverage (realCoordinatePermutationAction n q ι) T (a, i) =
      (∑ σ : Equiv.Perm (Fin q), T (a ∘ σ, i)) / q.factorial := by
  change (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : (Fin q → Fin n) × ι => ℝ) (a, i))
    ((Fintype.card (Equiv.Perm (Fin q)) : ℝ)⁻¹ •
      ∑ σ, realCoordinatePermutationAction n q ι σ T) = _
  rw [map_smul, map_sum, Fintype.card_perm, Fintype.card_fin]
  change (q.factorial : ℝ)⁻¹ * (∑ σ : Equiv.Perm (Fin q), T (a ∘ σ, i)) = _
  ring

variable {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
  {ι : Type*} [Fintype ι] (U : WeightedH1Family φ ι)
  (F : (k : ℕ) → WeightedIterationIndex n ι k → Space n → ℝ)
  (hF : ∀ k i, ContDiff ℝ (⊤ : ℕ∞) (F k i))
  (hV : ∀ k i, F k i =ᵐ[volume] (weightedH1Value φ
    (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U k i) : Space n → ℝ))

include hF hV

theorem weightedIteration_gradient_taylor_apply (k d : ℕ)
    (a : Fin (d + 1) → Fin n) (i : WeightedIterationIndex n ι k) :
    weightedL2GradientTaylor φ d
      (weightedFamilyCenteredGradient φ (WeightedIterationIndex n ι k)
        (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U k)) (a, i) =
      exponentialTiltCenteredGradientTaylor φ (F k i) d a := by
  rw [weightedL2GradientTaylor_apply]
  exact exponentialTiltCoordinateTaylor_congr_ae
    (weightedFamilyCenteredGradient_ae_of_representative (hφ.of_le (by simp))
      (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U k) (F k)
        (fun i => (hF k i).of_le (by simp)) (hV k) (a (Fin.last d), i)) d (Fin.init a)

/-- Corollary 3.7 is now an equality of the actual finite L2 Taylor tensors
under the literal isometric permutation action. -/
theorem weightedIteration_taylor_action_recursion
    (hL : ∀ k i, MemLp (weightedDiffusion φ (F k i)) 2 (potentialMeasure φ))
    (k : ℕ) {d : ℕ} (hd : d ≠ 0) :
    finiteIsometryAverage (realCoordinatePermutationAction n (d + 1)
      (WeightedIterationIndex n ι (k + 1)))
      (weightedL2GradientTaylor φ d
        (weightedFamilyCenteredGradient φ (WeightedIterationIndex n ι (k + 1))
          (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U (k + 1)))) =
      weightedSuccessorScale (hφ.of_le (by simp)) hκ hlower
        (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U k) •
          weightedL2TaylorTensor φ (d + 1)
            (weightedFamilyCenteredGradient φ (WeightedIterationIndex n ι k)
              (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U k)) := by
  apply PiLp.ext
  rintro ⟨a, ji⟩
  rw [realCoordinatePermutationAverage_apply]
  change (∑ σ : Equiv.Perm (Fin (d + 1)),
    weightedL2GradientTaylor φ d
      (weightedFamilyCenteredGradient φ (WeightedIterationIndex n ι (k + 1))
        (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U (k + 1))) (a ∘ σ, ji)) /
      (d + 1).factorial =
        weightedSuccessorScale (hφ.of_le (by simp)) hκ hlower
          (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U k) *
            exponentialTiltCoordinateTaylor φ
              (weightedFamilyCenteredGradient φ (WeightedIterationIndex n ι k)
                (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U k) ji) (d + 1) a
  simp_rw [weightedIteration_gradient_taylor_apply hφ hκ hlower U F hF hV]
  rw [exponentialTiltCoordinateTaylor_congr_ae
    (weightedFamilyCenteredGradient_ae_of_representative (hφ.of_le (by simp))
      (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U k) (F k)
        (fun i => (hF k i).of_le (by simp)) (hV k) ji) (d + 1) a]
  exact weightedIteration_centered_taylor_recursion hφ hκ hlower U F hF hV hL k hd ji a

end KLS
end

#print axioms KLS.realCoordinatePermutationAverage_apply
#print axioms KLS.weightedIteration_gradient_taylor_apply
#print axioms KLS.weightedIteration_taylor_action_recursion

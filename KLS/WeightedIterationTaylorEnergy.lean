import KLS.WeightedL2TaylorTensor
import KLS.WeightedSuccessorIteration

/-! Scalar notation for the squared norm of the actual Taylor tensor along
the actual iteration, with its elementary bound from the criterion premise. -/

open MeasureTheory Matrix
open scoped ContDiff RealInnerProductSpace Topology BigOperators
noncomputable section
namespace KLS
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
  {ι : Type*} [Fintype ι] (U : WeightedH1Family φ ι)

def weightedIterationTaylorEnergy (d k : ℕ) : ℝ :=
  ‖weightedL2TaylorTensor φ d
    (weightedFamilyCenteredGradient φ (WeightedIterationIndex n ι k)
      (weightedSuccessorIterate hφ hκ hlower U k))‖ ^ 2

theorem weightedIterationTaylorEnergy_nonneg (d k : ℕ) :
    0 ≤ weightedIterationTaylorEnergy hφ hκ hlower U d k := sq_nonneg _

/-- The criterion bound gives the actual next Dirichlet energy on the right,
since that energy is the centered-gradient norm squared by normalization. -/
theorem weightedIterationTaylorEnergy_le_next {R : ℝ} (hR : WeightedCoordinateTaylorBound φ R)
    {d : ℕ} (hd : 1 ≤ d) (k : ℕ) :
    weightedIterationTaylorEnergy hφ hκ hlower U d k ≤
      R ^ (2 * d) * weightedIterationEnergy hφ hκ hlower U (k + 1) := by
  have hn := congrArg (fun t : ℝ => t ^ 2)
    (weightedNormalizedSuccessor_gradient_norm hφ hκ hlower (weightedSuccessorIterate hφ hκ hlower U k))
  have he : weightedIterationEnergy hφ hκ hlower U (k + 1) =
      ‖weightedFamilyCenteredGradient φ (WeightedIterationIndex n ι k)
        (weightedSuccessorIterate hφ hκ hlower U k)‖ ^ 2 := hn
  rw [he]
  exact weightedL2TaylorTensor_norm_sq_le hR hd _

theorem weightedIterationTaylorEnergy_le_initial {R lam : ℝ}
    (hR : WeightedCoordinateTaylorBound φ R)
    (hE0 : weightedIterationEnergy hφ hκ hlower U 0 = lam)
    {d : ℕ} (hd : 1 ≤ d) (k : ℕ) :
    weightedIterationTaylorEnergy hφ hκ hlower U d k ≤ lam * R ^ (2 * d) := by
  have he := weightedIterationEnergy_antitone hφ hκ hlower U (Nat.zero_le (k + 1))
  rw [hE0] at he
  have hRpow : 0 ≤ R ^ (2 * d) := by rw [pow_mul]; exact pow_nonneg (sq_nonneg R) d
  exact (weightedIterationTaylorEnergy_le_next hφ hκ hlower U hR hd k).trans
    ((mul_le_mul_of_nonneg_left he hRpow).trans_eq (mul_comm _ _))

end KLS
end

#print axioms KLS.weightedIterationTaylorEnergy
#print axioms KLS.weightedIterationTaylorEnergy_le_next
#print axioms KLS.weightedIterationTaylorEnergy_le_initial

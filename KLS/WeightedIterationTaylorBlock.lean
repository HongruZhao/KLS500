import KLS.TaylorBlockIndices

/-! Actual Taylor tensors on one fixed coordinate carrier. The first d
positions are Taylor directions and the following q+1 are actual derivative
indices; their total m+1 is fixed while Taylor degree increases. -/

open MeasureTheory Matrix
open scoped ContDiff RealInnerProductSpace Topology BigOperators
noncomputable section
namespace KLS
variable {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
  {ι : Type*} [Fintype ι] (U : WeightedH1Family φ ι)

def weightedIterationBlockTaylor (r d q m : ℕ) (h : d + q = m) :
    EuclideanSpace ℝ ((Fin (m + 1) → Fin n) × WeightedIterationIndex n ι r) :=
  WithLp.toLp 2 (fun ai =>
    exponentialTiltCoordinateTaylor φ
      (weightedFamilyCenteredGradient φ (WeightedIterationIndex n ι (r + q))
        (weightedSuccessorIterate hφ hκ hlower U (r + q))
          ((tensorPrefixEquiv n ι r (q + 1)).symm
            (finBlockTuple ai.1 d (q + 1) (by omega), ai.2))) d
      (finBlockTuple ai.1 0 d (by omega)))

@[simp] theorem weightedIterationBlockTaylor_apply (r d q m : ℕ) (h : d + q = m)
    (a : Fin (m + 1) → Fin n) (i : WeightedIterationIndex n ι r) :
    weightedIterationBlockTaylor hφ hκ hlower U r d q m h (a, i) =
      exponentialTiltCoordinateTaylor φ
        (weightedFamilyCenteredGradient φ (WeightedIterationIndex n ι (r + q))
          (weightedSuccessorIterate hφ hκ hlower U (r + q))
            ((tensorPrefixEquiv n ι r (q + 1)).symm
              (finBlockTuple a d (q + 1) (by omega), i))) d
        (finBlockTuple a 0 d (by omega)) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Split the next derivative coordinate after the d Taylor coordinates,
leaving every remaining derivative index in its literal order. -/
theorem weightedIterationBlockTaylor_step_entry (r d q m : ℕ) (h : d + (q + 1) = m)
    (a : Fin (m + 1) → Fin n) (i : WeightedIterationIndex n ι r) :
    weightedIterationBlockTaylor hφ hκ hlower U r d (q + 1) m h (a, i) =
      weightedL2GradientTaylor φ d
        (weightedFamilyCenteredGradient φ (WeightedIterationIndex n ι (r + q + 1))
          (weightedSuccessorIterate hφ hκ hlower U (r + q + 1)))
        (finBlockTuple a 0 (d + 1) (by omega),
          (tensorPrefixEquiv n ι r (q + 1)).symm
            (finBlockTuple a (d + 1) (q + 1) (by omega), i)) := by
  rw [weightedIterationBlockTaylor_apply, weightedL2GradientTaylor_apply,
    tensorPrefixEquiv_succ_symm_apply, finBlockTuple_tail, finBlockTuple_head]
  simp only [finBlockTuple_init, finBlockTuple_last, Nat.zero_add]
  rfl

end KLS
end

#print axioms KLS.weightedIterationBlockTaylor
#print axioms KLS.weightedIterationBlockTaylor_step_entry

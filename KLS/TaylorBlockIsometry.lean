import KLS.WeightedIterationTaylorBlock

/-! Packing the Taylor and derivative coordinate blocks is a literal finite
index equivalence, hence preserves the full Euclidean tensor norm. -/

open MeasureTheory Matrix
open scoped ContDiff RealInnerProductSpace Topology BigOperators
noncomputable section
namespace KLS

def mergeTaylorBlockEquiv (n : ℕ) (ι : Type*) (r d q m : ℕ) (h : d + q = m) :
    ((Fin d → Fin n) × WeightedIterationIndex n ι (r + (q + 1))) ≃
      ((Fin (m + 1) → Fin n) × WeightedIterationIndex n ι r) :=
  (Equiv.prodCongr (Equiv.refl (Fin d → Fin n)) (tensorPrefixEquiv n ι r (q + 1))).trans
    ((Equiv.prodAssoc (Fin d → Fin n) (Fin (q + 1) → Fin n)
      (WeightedIterationIndex n ι r)).symm.trans
        (Equiv.prodCongr ((Fin.appendEquiv d (q + 1)).trans
          (Equiv.arrowCongr (finCongr (by omega : d + (q + 1) = m + 1)) (Equiv.refl (Fin n))))
            (Equiv.refl _)))

theorem mergeTaylorBlockEquiv_symm_apply (n : ℕ) (ι : Type*) (r d q m : ℕ) (h : d + q = m)
    (a : Fin (m + 1) → Fin n) (i : WeightedIterationIndex n ι r) :
    (mergeTaylorBlockEquiv n ι r d q m h).symm (a, i) =
      (finBlockTuple a 0 d (by omega),
        (tensorPrefixEquiv n ι r (q + 1)).symm (finBlockTuple a d (q + 1) (by omega), i)) := by
  apply Prod.ext
  · funext j
    apply congrArg a
    apply Fin.ext
    simp
  · rfl

variable {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
  {ι : Type*} [Fintype ι] (U : WeightedH1Family φ ι)

theorem weightedIterationBlockTaylor_eq_reindex (r d q m : ℕ) (h : d + q = m) :
    weightedIterationBlockTaylor hφ hκ hlower U r d q m h =
      finiteScalarReindex (mergeTaylorBlockEquiv n ι r d q m h)
        (weightedL2TaylorTensor φ d
          (weightedFamilyCenteredGradient φ (WeightedIterationIndex n ι (r + q))
            (weightedSuccessorIterate hφ hκ hlower U (r + q)))) := by
  apply PiLp.ext
  rintro ⟨a, i⟩
  rw [finiteScalarReindex_apply, mergeTaylorBlockEquiv_symm_apply]
  rfl

theorem norm_weightedIterationBlockTaylor (r d q m : ℕ) (h : d + q = m) :
    ‖weightedIterationBlockTaylor hφ hκ hlower U r d q m h‖ =
      ‖weightedL2TaylorTensor φ d
        (weightedFamilyCenteredGradient φ (WeightedIterationIndex n ι (r + q))
          (weightedSuccessorIterate hφ hκ hlower U (r + q)))‖ := by
  rw [weightedIterationBlockTaylor_eq_reindex, LinearIsometryEquiv.norm_map]
  rfl

end KLS
end

#print axioms KLS.mergeTaylorBlockEquiv
#print axioms KLS.weightedIterationBlockTaylor_eq_reindex
#print axioms KLS.norm_weightedIterationBlockTaylor

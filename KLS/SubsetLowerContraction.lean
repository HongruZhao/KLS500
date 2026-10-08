import KLS.TailSubsets

/-! All labeled subsets containing the distinguished direction obey the
same canonical contraction bound; the coordinate sums are reindexed by
an actual equivalence of the two groups of coordinate assignments. -/
open MeasureTheory Set Matrix
open scoped BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS
variable {n r : ℕ}

def subsetCoordinateEquiv (T : Finset (Fin r)) :
    ((Fin T.card → Fin n) × (Fin Tᶜ.card → Fin n)) ≃ (Fin r → Fin n) :=
  (Equiv.sumArrowEquivProdArrow (Fin T.card) (Fin Tᶜ.card) (Fin n)).symm.trans
    (Equiv.arrowCongr (finSumEquivOfFinset (s := T) rfl rfl) (Equiv.refl (Fin n)))

@[simp] theorem subsetCoordinateEquiv_left (T : Finset (Fin r))
    (α : Fin T.card → Fin n) (β : Fin Tᶜ.card → Fin n) (i : Fin T.card) :
    subsetCoordinateEquiv T (α,β) (T.orderEmbOfFin rfl i) = α i := by
  change Sum.elim α β ((finSumEquivOfFinset (s := T) rfl rfl).symm
    (finSumEquivOfFinset (s := T) rfl rfl (Sum.inl i))) = α i
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] theorem subsetCoordinateEquiv_right (T : Finset (Fin r))
    (α : Fin T.card → Fin n) (β : Fin Tᶜ.card → Fin n) (i : Fin Tᶜ.card) :
    subsetCoordinateEquiv T (α,β) (Tᶜ.orderEmbOfFin rfl i) = β i := by
  change Sum.elim α β ((finSumEquivOfFinset (s := T) rfl rfl).symm
    (finSumEquivOfFinset (s := T) rfl rfl (Sum.inr i))) = β i
  rw [Equiv.symm_apply_apply]
  rfl

end KLS
namespace KLS.AdaptiveLocalization
open KLS.TensorEnergy
variable {n r : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

def subsetLowerTensor (μ : Measure (Space n)) (r : ℕ) (u : Space n)
    (z : Fin (n+n*n) → ℝ) (S : Finset (Fin (r+1))) (γ : Fin r → Fin n) : ℝ :=
  subsetCumulantMultilinear (law μ (decodeState z).1 (decodeState z).2)
    (inverseSqrtDirection μ z) S
    (Fin.cons u (fun i => inverseSqrtDirection μ z (γ i)))

theorem subsetLowerTensor_headSubset (hμ : IsCompact μ.support)
    (u : Space n) (z : Fin (n+n*n) → ℝ) (T : Finset (Fin r))
    (α : Fin T.card → Fin n) (β : Fin Tᶜ.card → Fin n) :
    subsetLowerTensor μ r u z (headSubset T) (subsetCoordinateEquiv T (α,β)) =
      canonicalLowerContraction μ T.card Tᶜ.card u z α β := by
  let := law_isProbability hμ (decodeState z).1 (decodeState z).2
  have hν : IsCompact (law μ (decodeState z).1 (decodeState z).2).support := by
    rwa [support_law hμ]
  rw [subsetLowerTensor, subsetCumulantMultilinear_apply hν]
  simp only [maskedDirections_headSubset, maskedDirections_headSubset_compl]
  unfold canonicalLowerContraction
  apply Finset.sum_congr rfl
  intro k _
  rw [listCumulant_perm hν (((maskedDirections_perm_orderEmb _ T).cons u).cons _),
    listCumulant_perm hν ((maskedDirections_perm_orderEmb _ Tᶜ).cons _),
    ← List.ofFn_cons, listCumulant_cons_ofFn hν, listCumulant_cons_ofFn hν]
  simp only [subsetCoordinateEquiv_left, subsetCoordinateEquiv_right]

theorem subsetLowerTensor_square_le (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (u : Space n)
    (z : Fin (n+n*n) → ℝ) (T : Finset (Fin r)) {B : ℝ}
    (hB : ∀ v : Space n, cumulantEnergy μ Tᶜ.card v z ≤
      B * inner ℝ v (matrixAction (coordinateCovarianceMatrix μ z) v)) :
    (∑ γ : Fin r → Fin n, subsetLowerTensor μ r u z (headSubset T) γ ^ 2) ≤
      B * cumulantEnergy μ (T.card+1) u z := by
  rw [← (subsetCoordinateEquiv (n := n) T).sum_comp]
  simp only [Fintype.sum_prod_type, subsetLowerTensor_headSubset hμ]
  exact canonicalLowerContraction_square_le hμ hfull u z hB

end KLS.AdaptiveLocalization
end

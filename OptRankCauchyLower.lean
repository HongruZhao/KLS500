import KLS.LowerCumulantSubsetSum
import OptRankWeights

/-! Positive weights on the subset cardinalities retain the exact
Cauchy--Schwarz cost of the different lower-cumulant contributions. -/
open MeasureTheory Set Matrix
open scoped BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS.AdaptiveLocalization
open KLS.TensorEnergy
variable {n r : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

theorem lowerCumulant_square_le_rankWeighted_energies (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (hr : 2 ≤ r)
    (u : Space n) (z : Fin (n+n*n) → ℝ) (B : Finset (Fin r) → ℝ)
    (w : ℕ → ℝ) (hw : ∀ j, 0 < w j)
    (hB : ∀ T ∈ activeTailSubsets r, ∀ v : Space n,
      cumulantEnergy μ Tᶜ.card v z ≤ B T * inner ℝ v (matrixAction (coordinateCovarianceMatrix μ z) v)) :
    (whitenedLowerCumulantTensor μ r u z ⬝ᵥ whitenedLowerCumulantTensor μ r u z) ≤
      (∑ j ∈ Finset.Icc 1 (r-2), w j) * ∑ T ∈ activeTailSubsets r,
        (B T / (subsetBinomialWeight T * w T.card)) * cumulantEnergy μ (T.card+1) u z := by
  let p := fun T γ => subsetLowerTensor μ r u z (headSubset T) γ
  let v := fun T : Finset (Fin r) => subsetBinomialWeight T * w T.card
  have hv (T : Finset (Fin r)) : 0 < v T := mul_pos (subsetBinomialWeight_pos T) (hw _)
  have hsum : (∑ T ∈ activeTailSubsets r, v T) = ∑ j ∈ Finset.Icc 1 (r-2), w j :=
    sum_subsetBinomialWeight_mul_card w
  have hc (γ : Fin r → Fin n) :
      (∑ T ∈ activeTailSubsets r, p T γ)^2 ≤
        (∑ T ∈ activeTailSubsets r, v T) * ∑ T ∈ activeTailSubsets r, p T γ^2 / v T := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _
      (fun T _ => (hv T).le) (fun T _ => div_nonneg (sq_nonneg _) (hv T).le)
    intro T _
    rw [mul_div_cancel₀ _ (hv T).ne']
  unfold dotProduct
  simp_rw [← pow_two, whitenedLowerCumulantTensor_eq_subset_sum hμ hr]
  change (∑ γ, (∑ T ∈ activeTailSubsets r, p T γ)^2) ≤ _
  calc
    _ ≤ ∑ γ : Fin r → Fin n, (∑ T ∈ activeTailSubsets r, v T) *
        ∑ T ∈ activeTailSubsets r, p T γ^2 / v T := Finset.sum_le_sum fun γ _ => hc γ
    _ = (∑ j ∈ Finset.Icc 1 (r-2), w j) * ∑ T ∈ activeTailSubsets r,
        (∑ γ : Fin r → Fin n, p T γ^2) / v T := by
      rw [← Finset.mul_sum, hsum]
      congr 1
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => (Finset.sum_div _ _ _).symm
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg fun j _ => (hw j).le)
      apply Finset.sum_le_sum
      intro T hT
      have hh := div_le_div_of_nonneg_right
        (subsetLowerTensor_square_le hμ hfull u z T (hB T hT)) (hv T).le
      exact hh.trans_eq (by dsimp [v]; ring)

end KLS.AdaptiveLocalization
end

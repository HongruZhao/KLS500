import KLS.SubsetLowerContraction
import KLS.CumulantFactorialMajorant

/-! The true whitened lower tensor is the sum over all labeled tail
subsets. Positive binomial weights give the sharp factorial-compatible
finite Cauchy--Schwarz estimate used before time integration. -/
open MeasureTheory Set Matrix
open scoped BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS
variable {r : ℕ}

theorem sum_headSubset (f : Finset (Fin (r+1)) → ℝ) :
    (∑ S : Finset (Fin (r+1)), if 0 ∈ S then f S else 0) =
      ∑ T : Finset (Fin r), f (headSubset T) := by
  rw [← Finset.sum_filter, Finset.sum_subtype (p := fun S : Finset (Fin (r+1)) => 0 ∈ S) _ (by intro S; simp)]
  exact ((headSubsetEquiv r).sum_comp (fun S => f S.1)).symm

end KLS
namespace KLS.AdaptiveLocalization
open KLS.TensorEnergy
variable {n r : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

theorem whitenedLowerCumulantTensor_eq_subset_sum (hμ : IsCompact μ.support)
    (hr : 2 ≤ r) (u : Space n) (z : Fin (n+n*n) → ℝ) (γ : Fin r → Fin n) :
    whitenedLowerCumulantTensor μ r u z γ =
      ∑ T ∈ activeTailSubsets r, subsetLowerTensor μ r u z (headSubset T) γ := by
  rw [whitenedLowerCumulantTensor_eq_evaluation hμ, ← lowerCumulantMultilinear_apply hμ,
    lowerCumulantMultilinear, _root_.sum_apply]
  calc
    _ = ∑ S : Finset (Fin (r+1)), if 0 ∈ S then
        (if 2 ≤ S.card ∧ S.card ≤ (r+1)-2 then subsetLowerTensor μ r u z S γ else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro S _
      by_cases h0 : (0 : Fin (r+1)) ∈ S
      · simp only [h0, true_and, ite_true]
        split_ifs <;> rfl
      · simp only [h0, false_and, ite_false, _root_.zero_apply]
    _ = ∑ T : Finset (Fin r), if 2 ≤ (headSubset T).card ∧
        (headSubset T).card ≤ (r+1)-2 then subsetLowerTensor μ r u z (headSubset T) γ else 0 :=
      sum_headSubset _
    _ = _ := by
      rw [activeTailSubsets, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro T _
      have he : (2 ≤ T.card+1 ∧ T.card+1 ≤ (r+1)-2) ↔
          (1 ≤ T.card ∧ T.card ≤ r-2) := by omega
      simp only [card_headSubset, he]

theorem lowerCumulant_square_le_weighted_energies (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (hr : 2 ≤ r)
    (u : Space n) (z : Fin (n+n*n) → ℝ) (B : Finset (Fin r) → ℝ)
    (hB : ∀ T ∈ activeTailSubsets r, ∀ v : Space n,
      cumulantEnergy μ Tᶜ.card v z ≤ B T * inner ℝ v (matrixAction (coordinateCovarianceMatrix μ z) v)) :
    (whitenedLowerCumulantTensor μ r u z ⬝ᵥ whitenedLowerCumulantTensor μ r u z) ≤
      (r-2 : ℕ) * ∑ T ∈ activeTailSubsets r,
        (B T / subsetBinomialWeight T) * cumulantEnergy μ (T.card+1) u z := by
  let p := fun T γ => subsetLowerTensor μ r u z (headSubset T) γ
  let w := fun T : Finset (Fin r) => subsetBinomialWeight T
  have hc (γ : Fin r → Fin n) :
      (∑ T ∈ activeTailSubsets r, p T γ)^2 ≤
        (∑ T ∈ activeTailSubsets r, w T) * ∑ T ∈ activeTailSubsets r, p T γ^2 / w T := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _
      (fun T _ => (subsetBinomialWeight_pos T).le)
      (fun T _ => div_nonneg (sq_nonneg _) (subsetBinomialWeight_pos T).le)
    intro T _
    rw [mul_div_cancel₀ _ (subsetBinomialWeight_pos T).ne']
  unfold dotProduct
  simp_rw [← pow_two, whitenedLowerCumulantTensor_eq_subset_sum hμ hr]
  change (∑ γ, (∑ T ∈ activeTailSubsets r, p T γ)^2) ≤ _
  calc
    _ ≤ ∑ γ : Fin r → Fin n, (∑ T ∈ activeTailSubsets r, w T) *
        ∑ T ∈ activeTailSubsets r, p T γ^2 / w T := Finset.sum_le_sum fun γ _ => hc γ
    _ = (r-2 : ℕ) * ∑ T ∈ activeTailSubsets r, (∑ γ : Fin r → Fin n, p T γ^2) / w T := by
      rw [← Finset.mul_sum, sum_subsetBinomialWeight]
      congr 1
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => (Finset.sum_div _ _ _).symm
    _ ≤ _ := by
      gcongr with T hT
      have hh := div_le_div_of_nonneg_right
        (subsetLowerTensor_square_le hμ hfull u z T (hB T hT))
        (subsetBinomialWeight_pos T).le
      exact hh.trans_eq (by ring)

end KLS.AdaptiveLocalization
end

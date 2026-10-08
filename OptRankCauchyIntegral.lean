import OptRankCauchyLower
import OptMixedLowerContraction

/-! The rank-weighted tensor estimate is integrated against the genuine
process product measure, preserving the separate compact and time weights. -/
open MeasureTheory Set Matrix Filter
open scoped BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS.AdaptiveLocalization
open KLS.TensorEnergy
variable {n r : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]
  {X : Type*} [MeasurableSpace X] {ξ : Measure X}

theorem integrated_rankWeighted_lowerCumulant_square_le (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (hr : 2 ≤ r)
    {α K : ℝ} (hα : 0 ≤ α) (hK : 0 < K) (qC : ℕ → ℝ) (hqC : ∀ j, 0 ≤ qC j)
    (qI : ℕ → ℝ) (β : ℝ) (w : ℕ → ℝ) (hw : ∀ j, 0 < w j)
    (u : Space n) (Z : X → (Fin (n+n*n) → ℝ))
    (hL : AEStronglyMeasurable (fun x => whitenedLowerCumulantTensor μ r u (Z x) ⬝ᵥ
      whitenedLowerCumulantTensor μ r u (Z x)) ξ)
    (hE : ∀ T ∈ activeTailSubsets r, Integrable (fun x => cumulantEnergy μ (T.card+1) u (Z x)) ξ)
    (hB : ∀ᵐ x ∂ξ, ∀ T ∈ activeTailSubsets r, ∀ v : Space n,
      cumulantEnergy μ Tᶜ.card v (Z x) ≤ (α * qC Tᶜ.card * cumulantEnergyMajorant K Tᶜ.card) *
        inner ℝ v (matrixAction (coordinateCovarianceMatrix μ (Z x)) v))
    (hI : ∀ T ∈ activeTailSubsets r,
      (∫ x, cumulantEnergy μ (T.card+1) u (Z x) ∂ξ) ≤
        β * (α * qI T.card * cumulantEnergyMajorant K T.card) * ‖u‖^2) :
    (∫ x, whitenedLowerCumulantTensor μ r u (Z x) ⬝ᵥ
      whitenedLowerCumulantTensor μ r u (Z x) ∂ξ) ≤
        β * α^2 * cumulantEnergyMajorant K r * ‖u‖^2 *
          (∑ j ∈ Finset.Icc 1 (r-2), w j) *
          (∑ j ∈ Finset.Icc 1 (r-2), qI j * qC (r-j) / w j) := by
  let S := ∑ j ∈ Finset.Icc 1 (r-2), w j
  have hS : 0 ≤ S := Finset.sum_nonneg fun j _ => (hw j).le
  let G := fun x => S * ∑ T ∈ activeTailSubsets r,
    ((α * qC Tᶜ.card * cumulantEnergyMajorant K Tᶜ.card) /
      (subsetBinomialWeight T * w T.card)) * cumulantEnergy μ (T.card+1) u (Z x)
  have hf := weighted_lowerCumulant_square_integrable hμ hfull hr α K qC u Z hL hE hB
  have hg : Integrable G ξ :=
    (integrable_finsetSum _ fun T hT => (hE T hT).const_mul _).const_mul _
  calc
    _ ≤ ∫ x, G x ∂ξ := integral_mono_ae hf hg (hB.mono fun x hx =>
        lowerCumulant_square_le_rankWeighted_energies hμ hfull hr u (Z x) _ w hw hx)
    _ = S * ∑ T ∈ activeTailSubsets r,
        ((α * qC Tᶜ.card * cumulantEnergyMajorant K Tᶜ.card) /
          (subsetBinomialWeight T * w T.card)) *
          (∫ x, cumulantEnergy μ (T.card+1) u (Z x) ∂ξ) := by
      simp only [G]
      rw [integral_const_mul, integral_finsetSum]
      · simp only [integral_const_mul]
      · exact fun T hT => (hE T hT).const_mul _
    _ ≤ S * ∑ T ∈ activeTailSubsets r,
        ((α * qC Tᶜ.card * cumulantEnergyMajorant K Tᶜ.card) /
          (subsetBinomialWeight T * w T.card)) *
          (β * (α * qI T.card * cumulantEnergyMajorant K T.card) * ‖u‖^2) := by
      apply mul_le_mul_of_nonneg_left _ hS
      apply Finset.sum_le_sum
      intro T hT
      exact mul_le_mul_of_nonneg_left (hI T hT)
        (div_nonneg (mul_nonneg (mul_nonneg hα (hqC _)) (cumulantEnergyMajorant_pos hK _).le)
          (mul_nonneg (subsetBinomialWeight_pos T).le (hw _).le))
    _ = _ := by
      have he (T : Finset (Fin r)) :
          ((α * qC Tᶜ.card * cumulantEnergyMajorant K Tᶜ.card) /
            (subsetBinomialWeight T * w T.card)) *
            (β * (α * qI T.card * cumulantEnergyMajorant K T.card) * ‖u‖^2) =
              (β * α^2 * cumulantEnergyMajorant K r * ‖u‖^2) *
                (subsetBinomialWeight T * (qI T.card * qC (r-T.card) / w T.card)) := by
        have hcompl : Tᶜ.card = r-T.card := by rw [Finset.card_compl, Fintype.card_fin]
        calc
          _ = ((β/2) * α^2 * qI T.card * qC Tᶜ.card *
              ((cumulantEnergyMajorant K Tᶜ.card / subsetBinomialWeight T) *
              (2 * cumulantEnergyMajorant K T.card)) * ‖u‖^2) / w T.card := by
                simp only [div_mul_eq_div_div]
                ring
          _ = _ := by rw [majorant_div_weight_mul_lower, hcompl]; ring
      rw [Finset.sum_congr rfl (fun T _ => he T), ← Finset.mul_sum,
        sum_subsetBinomialWeight_mul_card (r := r) (fun j => qI j * qC (r-j) / w j)]
      dsimp [S]
      ring

end KLS.AdaptiveLocalization
end

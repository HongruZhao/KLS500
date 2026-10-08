import OptWeightedLowerContractionBeta

/-! Actual product-space lower-cumulant integrability and (106). The
probability/time product can be any measure here; the only analytic inputs
are integrability of the genuine smaller-order energies and their stated
integral bounds. All subset domination and factorial cancellation are proved. -/
open MeasureTheory Set Matrix Filter
open scoped BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS.AdaptiveLocalization
open KLS.TensorEnergy
variable {n r : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]
  {X : Type*} [MeasurableSpace X] {ξ : Measure X}

theorem integrated_mixed_lowerCumulant_square_le (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (hr : 2 ≤ r)
    {α K : ℝ} (hα : 0 ≤ α) (hK : 0 < K) (qC : ℕ → ℝ) (hqC : ∀ j, 0 ≤ qC j) (qI : ℕ → ℝ) (β : ℝ) (u : Space n) (Z : X → (Fin (n+n*n) → ℝ))
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
        β * α^2 * ((r-2 : ℕ) : ℝ) * cumulantEnergyMajorant K r * ‖u‖^2 *
          (∑ j ∈ Finset.Icc 1 (r-2), qI j * qC (r-j)) := by
  have hf := weighted_lowerCumulant_square_integrable hμ hfull hr α K qC u Z hL hE hB
  have hg := integrable_weightedLowerCumulantMajorantFunction α K qC u Z hE
  calc
    _ ≤ ∫ x, weightedLowerCumulantMajorantFunction μ r α K qC u (Z x) ∂ξ :=
      integral_mono_ae hf hg (hB.mono fun x hx =>
        lowerCumulant_square_le_weighted_energies hμ hfull hr u (Z x) _ hx)
    _ = (r-2 : ℕ) * ∑ T ∈ activeTailSubsets r,
        ((α * qC Tᶜ.card * cumulantEnergyMajorant K Tᶜ.card) / subsetBinomialWeight T) *
          (∫ x, cumulantEnergy μ (T.card+1) u (Z x) ∂ξ) := by
      simp only [weightedLowerCumulantMajorantFunction]
      rw [integral_const_mul, integral_finsetSum]
      · simp only [integral_const_mul]
      · exact fun T hT => (hE T hT).const_mul _
    _ ≤ (r-2 : ℕ) * ∑ T ∈ activeTailSubsets r,
        ((α * qC Tᶜ.card * cumulantEnergyMajorant K Tᶜ.card) / subsetBinomialWeight T) *
          (β * (α * qI T.card * cumulantEnergyMajorant K T.card) * ‖u‖^2) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro T hT
      exact mul_le_mul_of_nonneg_left (hI T hT)
        (div_nonneg (mul_nonneg (mul_nonneg hα (hqC _)) (cumulantEnergyMajorant_pos hK _).le) (subsetBinomialWeight_pos T).le)
    _ = _ := by
      have he (T : Finset (Fin r)) :
          ((α * qC Tᶜ.card * cumulantEnergyMajorant K Tᶜ.card) / subsetBinomialWeight T) *
            (β * (α * qI T.card * cumulantEnergyMajorant K T.card) * ‖u‖^2) =
              (β * α^2 * cumulantEnergyMajorant K r * ‖u‖^2) *
                (subsetBinomialWeight T * (qI T.card * qC (r-T.card))) := by
        have hcompl : Tᶜ.card = r-T.card := by rw [Finset.card_compl, Fintype.card_fin]
        calc
          _ = (β/2) * α^2 * qI T.card * qC Tᶜ.card *
              ((cumulantEnergyMajorant K Tᶜ.card / subsetBinomialWeight T) *
              (2 * cumulantEnergyMajorant K T.card)) * ‖u‖^2 := by ring
          _ = _ := by rw [majorant_div_weight_mul_lower, hcompl]; ring
      rw [Finset.sum_congr rfl (fun T _ => he T), ← Finset.mul_sum,
        sum_subsetBinomialWeight_mul_card (r := r) (fun j => qI j * qC (r-j))]
      ring

end KLS.AdaptiveLocalization
end

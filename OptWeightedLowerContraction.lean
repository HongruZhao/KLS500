import OptScaledLowerContraction
import OptRankWeights

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

def weightedLowerCumulantMajorantFunction (μ : Measure (Space n)) (r : ℕ) (α K : ℝ) (q : ℕ → ℝ) (u : Space n)
    (z : Fin (n+n*n) → ℝ) : ℝ :=
  (r-2 : ℕ) * ∑ T ∈ activeTailSubsets r,
    ((α * q Tᶜ.card * cumulantEnergyMajorant K Tᶜ.card) / subsetBinomialWeight T) * cumulantEnergy μ (T.card+1) u z

omit [IsProbabilityMeasure μ] in
theorem integrable_weightedLowerCumulantMajorantFunction (α K : ℝ) (q : ℕ → ℝ) (u : Space n)
    (Z : X → (Fin (n+n*n) → ℝ))
    (hE : ∀ T ∈ activeTailSubsets r, Integrable (fun x => cumulantEnergy μ (T.card+1) u (Z x)) ξ) :
    Integrable (fun x => weightedLowerCumulantMajorantFunction μ r α K q u (Z x)) ξ := by
  exact (integrable_finsetSum _ fun T hT => (hE T hT).const_mul _).const_mul _

theorem weighted_lowerCumulant_square_integrable (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (hr : 2 ≤ r)
    (α K : ℝ) (q : ℕ → ℝ) (u : Space n) (Z : X → (Fin (n+n*n) → ℝ))
    (hL : AEStronglyMeasurable (fun x => whitenedLowerCumulantTensor μ r u (Z x) ⬝ᵥ
      whitenedLowerCumulantTensor μ r u (Z x)) ξ)
    (hE : ∀ T ∈ activeTailSubsets r, Integrable (fun x => cumulantEnergy μ (T.card+1) u (Z x)) ξ)
    (hB : ∀ᵐ x ∂ξ, ∀ T ∈ activeTailSubsets r, ∀ v : Space n,
      cumulantEnergy μ Tᶜ.card v (Z x) ≤ (α * q Tᶜ.card * cumulantEnergyMajorant K Tᶜ.card) *
        inner ℝ v (matrixAction (coordinateCovarianceMatrix μ (Z x)) v)) :
    Integrable (fun x => whitenedLowerCumulantTensor μ r u (Z x) ⬝ᵥ
      whitenedLowerCumulantTensor μ r u (Z x)) ξ := by
  apply (integrable_weightedLowerCumulantMajorantFunction α K q u Z hE).mono' hL
  filter_upwards [hB] with x hx
  rw [Real.norm_of_nonneg (dotProduct_self_nonnegative _)]
  exact lowerCumulant_square_le_weighted_energies hμ hfull hr u (Z x) _ hx

theorem integrated_weighted_lowerCumulant_square_le (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (hr : 2 ≤ r)
    {α K : ℝ} (hα : 0 ≤ α) (hK : 0 < K) (q : ℕ → ℝ) (hq : ∀ j, 0 ≤ q j) (u : Space n) (Z : X → (Fin (n+n*n) → ℝ))
    (hL : AEStronglyMeasurable (fun x => whitenedLowerCumulantTensor μ r u (Z x) ⬝ᵥ
      whitenedLowerCumulantTensor μ r u (Z x)) ξ)
    (hE : ∀ T ∈ activeTailSubsets r, Integrable (fun x => cumulantEnergy μ (T.card+1) u (Z x)) ξ)
    (hB : ∀ᵐ x ∂ξ, ∀ T ∈ activeTailSubsets r, ∀ v : Space n,
      cumulantEnergy μ Tᶜ.card v (Z x) ≤ (α * q Tᶜ.card * cumulantEnergyMajorant K Tᶜ.card) *
        inner ℝ v (matrixAction (coordinateCovarianceMatrix μ (Z x)) v))
    (hI : ∀ T ∈ activeTailSubsets r,
      (∫ x, cumulantEnergy μ (T.card+1) u (Z x) ∂ξ) ≤
        2 * (α * q T.card * cumulantEnergyMajorant K T.card) * ‖u‖^2) :
    (∫ x, whitenedLowerCumulantTensor μ r u (Z x) ⬝ᵥ
      whitenedLowerCumulantTensor μ r u (Z x) ∂ξ) ≤
        2 * α^2 * ((r-2 : ℕ) : ℝ) * cumulantEnergyMajorant K r * ‖u‖^2 *
          (∑ j ∈ Finset.Icc 1 (r-2), q j * q (r-j)) := by
  have hf := weighted_lowerCumulant_square_integrable hμ hfull hr α K q u Z hL hE hB
  have hg := integrable_weightedLowerCumulantMajorantFunction α K q u Z hE
  calc
    _ ≤ ∫ x, weightedLowerCumulantMajorantFunction μ r α K q u (Z x) ∂ξ :=
      integral_mono_ae hf hg (hB.mono fun x hx =>
        lowerCumulant_square_le_weighted_energies hμ hfull hr u (Z x) _ hx)
    _ = (r-2 : ℕ) * ∑ T ∈ activeTailSubsets r,
        ((α * q Tᶜ.card * cumulantEnergyMajorant K Tᶜ.card) / subsetBinomialWeight T) *
          (∫ x, cumulantEnergy μ (T.card+1) u (Z x) ∂ξ) := by
      simp only [weightedLowerCumulantMajorantFunction]
      rw [integral_const_mul, integral_finsetSum]
      · simp only [integral_const_mul]
      · exact fun T hT => (hE T hT).const_mul _
    _ ≤ (r-2 : ℕ) * ∑ T ∈ activeTailSubsets r,
        ((α * q Tᶜ.card * cumulantEnergyMajorant K Tᶜ.card) / subsetBinomialWeight T) *
          (2 * (α * q T.card * cumulantEnergyMajorant K T.card) * ‖u‖^2) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro T hT
      exact mul_le_mul_of_nonneg_left (hI T hT)
        (div_nonneg (mul_nonneg (mul_nonneg hα (hq _)) (cumulantEnergyMajorant_pos hK _).le) (subsetBinomialWeight_pos T).le)
    _ = _ := by
      have he (T : Finset (Fin r)) :
          ((α * q Tᶜ.card * cumulantEnergyMajorant K Tᶜ.card) / subsetBinomialWeight T) *
            (2 * (α * q T.card * cumulantEnergyMajorant K T.card) * ‖u‖^2) =
              (2 * α^2 * cumulantEnergyMajorant K r * ‖u‖^2) *
                (subsetBinomialWeight T * (q T.card * q (r-T.card))) := by
        have hcompl : Tᶜ.card = r-T.card := by rw [Finset.card_compl, Fintype.card_fin]
        calc
          _ = α^2 * q T.card * q Tᶜ.card *
              ((cumulantEnergyMajorant K Tᶜ.card / subsetBinomialWeight T) *
              (2 * cumulantEnergyMajorant K T.card)) * ‖u‖^2 := by ring
          _ = _ := by rw [majorant_div_weight_mul_lower, hcompl]; ring
      rw [Finset.sum_congr rfl (fun T _ => he T), ← Finset.mul_sum,
        sum_subsetBinomialWeight_mul_card (r := r) (fun j => q j * q (r-j))]
      ring

end KLS.AdaptiveLocalization
end

import KLS.CompactCumulantEnergyBound

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

def lowerCumulantMajorantFunction (μ : Measure (Space n)) (r : ℕ) (K : ℝ) (u : Space n)
    (z : Fin (n+n*n) → ℝ) : ℝ :=
  (r-2 : ℕ) * ∑ T ∈ activeTailSubsets r,
    (cumulantEnergyMajorant K Tᶜ.card / subsetBinomialWeight T) * cumulantEnergy μ (T.card+1) u z

omit [IsProbabilityMeasure μ] in
theorem integrable_lowerCumulantMajorantFunction (K : ℝ) (u : Space n)
    (Z : X → (Fin (n+n*n) → ℝ))
    (hE : ∀ T ∈ activeTailSubsets r, Integrable (fun x => cumulantEnergy μ (T.card+1) u (Z x)) ξ) :
    Integrable (fun x => lowerCumulantMajorantFunction μ r K u (Z x)) ξ := by
  exact (integrable_finsetSum _ fun T hT => (hE T hT).const_mul _).const_mul _

theorem lowerCumulant_square_integrable (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (hr : 2 ≤ r)
    (K : ℝ) (u : Space n) (Z : X → (Fin (n+n*n) → ℝ))
    (hL : AEStronglyMeasurable (fun x => whitenedLowerCumulantTensor μ r u (Z x) ⬝ᵥ
      whitenedLowerCumulantTensor μ r u (Z x)) ξ)
    (hE : ∀ T ∈ activeTailSubsets r, Integrable (fun x => cumulantEnergy μ (T.card+1) u (Z x)) ξ)
    (hB : ∀ᵐ x ∂ξ, ∀ T ∈ activeTailSubsets r, ∀ v : Space n,
      cumulantEnergy μ Tᶜ.card v (Z x) ≤ cumulantEnergyMajorant K Tᶜ.card *
        inner ℝ v (matrixAction (coordinateCovarianceMatrix μ (Z x)) v)) :
    Integrable (fun x => whitenedLowerCumulantTensor μ r u (Z x) ⬝ᵥ
      whitenedLowerCumulantTensor μ r u (Z x)) ξ := by
  apply (integrable_lowerCumulantMajorantFunction K u Z hE).mono' hL
  filter_upwards [hB] with x hx
  rw [Real.norm_of_nonneg (dotProduct_self_nonnegative _)]
  exact lowerCumulant_square_le_weighted_energies hμ hfull hr u (Z x) _ hx

theorem integrated_lowerCumulant_square_le (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (hr : 2 ≤ r)
    {K : ℝ} (hK : 0 < K) (u : Space n) (Z : X → (Fin (n+n*n) → ℝ))
    (hL : AEStronglyMeasurable (fun x => whitenedLowerCumulantTensor μ r u (Z x) ⬝ᵥ
      whitenedLowerCumulantTensor μ r u (Z x)) ξ)
    (hE : ∀ T ∈ activeTailSubsets r, Integrable (fun x => cumulantEnergy μ (T.card+1) u (Z x)) ξ)
    (hB : ∀ᵐ x ∂ξ, ∀ T ∈ activeTailSubsets r, ∀ v : Space n,
      cumulantEnergy μ Tᶜ.card v (Z x) ≤ cumulantEnergyMajorant K Tᶜ.card *
        inner ℝ v (matrixAction (coordinateCovarianceMatrix μ (Z x)) v))
    (hI : ∀ T ∈ activeTailSubsets r,
      (∫ x, cumulantEnergy μ (T.card+1) u (Z x) ∂ξ) ≤
        2 * cumulantEnergyMajorant K T.card * ‖u‖^2) :
    (∫ x, whitenedLowerCumulantTensor μ r u (Z x) ⬝ᵥ
      whitenedLowerCumulantTensor μ r u (Z x) ∂ξ) ≤
        2 * ((r-2 : ℕ) : ℝ)^2 * cumulantEnergyMajorant K r * ‖u‖^2 := by
  have hf := lowerCumulant_square_integrable hμ hfull hr K u Z hL hE hB
  have hg := integrable_lowerCumulantMajorantFunction K u Z hE
  calc
    _ ≤ ∫ x, lowerCumulantMajorantFunction μ r K u (Z x) ∂ξ :=
      integral_mono_ae hf hg (hB.mono fun x hx =>
        lowerCumulant_square_le_weighted_energies hμ hfull hr u (Z x) _ hx)
    _ = (r-2 : ℕ) * ∑ T ∈ activeTailSubsets r,
        (cumulantEnergyMajorant K Tᶜ.card / subsetBinomialWeight T) *
          (∫ x, cumulantEnergy μ (T.card+1) u (Z x) ∂ξ) := by
      simp only [lowerCumulantMajorantFunction]
      rw [integral_const_mul, integral_finsetSum]
      · simp only [integral_const_mul]
      · exact fun T hT => (hE T hT).const_mul _
    _ ≤ (r-2 : ℕ) * ∑ T ∈ activeTailSubsets r,
        (cumulantEnergyMajorant K Tᶜ.card / subsetBinomialWeight T) *
          (2 * cumulantEnergyMajorant K T.card * ‖u‖^2) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro T hT
      exact mul_le_mul_of_nonneg_left (hI T hT)
        (div_nonneg (cumulantEnergyMajorant_pos hK _).le (subsetBinomialWeight_pos T).le)
    _ = _ := by
      have he (T : Finset (Fin r)) :
          (cumulantEnergyMajorant K Tᶜ.card / subsetBinomialWeight T) *
            (2 * cumulantEnergyMajorant K T.card * ‖u‖^2) =
              (2 * cumulantEnergyMajorant K r * ‖u‖^2) * subsetBinomialWeight T := by
        rw [← mul_assoc, majorant_div_weight_mul_lower]
        ring
      rw [Finset.sum_congr rfl (fun T _ => he T), ← Finset.mul_sum, sum_subsetBinomialWeight]
      ring

end KLS.AdaptiveLocalization
end

import KLS.TensorCoordinateExpansion

/-! The actual differential energy inequality, isolating only the genuine
third-cumulant matrix estimate still needed for a universal application. -/
open MeasureTheory ProbabilityTheory Matrix Set
open scoped BigOperators Matrix.Norms.Elementwise Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS.AdaptiveLocalization
open KLS.TensorEnergy
variable {n r : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

theorem cumulantEnergy_drift_lower (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (hr : 2 ≤ r)
    (u : Space n) (z : Fin (n+n*n) → ℝ) (K : ℝ)
    (hK : (K • (1 : Matrix (Fin n) (Fin n) ℝ) -
      ∑ k, whitenedCovarianceNoiseMatrix μ k z * whitenedCovarianceNoiseMatrix μ k z).PosSemidef) :
    (1/2 : ℝ) * cumulantEnergy μ (r+1) u z -
      (((r+2 : ℕ) : ℝ) + 2*K*(r : ℝ)^2) * cumulantEnergy μ r u z -
      2 * (whitenedCumulantTensor μ r u z ⬝ᵥ whitenedLowerCumulantTensor μ r u z) ≤
      differentialGenerator (coordinateDrift μ z) (fun k => coordinateDiffusion μ k z)
        (cumulantEnergy μ r u) z := by
  have h := cumulantEnergy_generator_lower_of_matrix_seed hμ hfull hr u z K hK
  rwa [sum_whitenedNextCumulantTensor_square hμ hfull] at h

/-- The paper's numerical energy estimate with C=17, conditional only on
its displayed genuine normalized third-cumulant matrix estimate. -/
theorem cumulantEnergy_drift_lower_of_seed_eight (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (hr : 2 ≤ r)
    (u : Space n) (z : Fin (n+n*n) → ℝ)
    (hK : ((8 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) -
      ∑ k, whitenedCovarianceNoiseMatrix μ k z * whitenedCovarianceNoiseMatrix μ k z).PosSemidef) :
    (1/2 : ℝ) * cumulantEnergy μ (r+1) u z -
      17 * ((r+1 : ℕ) : ℝ)^2 * cumulantEnergy μ r u z -
      2 * (whitenedCumulantTensor μ r u z ⬝ᵥ whitenedLowerCumulantTensor μ r u z) ≤
      differentialGenerator (coordinateDrift μ z) (fun k => coordinateDiffusion μ k z)
        (cumulantEnergy μ r u) z := by
  have h := cumulantEnergy_drift_lower hμ hfull hr u z 8 hK
  have hn := cumulantEnergy_nonnegative (r := r) hμ hfull u z
  have hcoef : ((r+2 : ℕ) : ℝ) + 2*8*(r : ℝ)^2 ≤ 17*((r+1 : ℕ) : ℝ)^2 := by
    push_cast
    nlinarith [sq_nonneg (r : ℝ), Nat.cast_nonneg (α := ℝ) r]
  have hc := mul_le_mul_of_nonneg_right hcoef hn
  nlinarith

end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.cumulantEnergy_drift_lower_of_seed_eight

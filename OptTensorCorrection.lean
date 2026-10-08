import KLS.AdaptiveEnergyDriftBound

/-! Retaining the positive squared slot-sum term sharpens the noise
penalty from two to three halves without changing the next-energy factor. -/
open Matrix MeasureTheory Set
open scoped BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS.TensorEnergy
variable {n r q : ℕ}

theorem energyNoiseCorrection_lower_three_halves (T : (Fin r → Fin n) → ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (W : (Fin r → Fin n) → ℝ) :
    (1/2 : ℝ) * (W ⬝ᵥ W) - (3/2 : ℝ) * ((tensorSlotSum H *ᵥ T) ⬝ᵥ (tensorSlotSum H *ᵥ T)) ≤
      energyNoiseCorrection T H W := by
  have hYoung := two_dotProduct_le W (tensorSlotSum H *ᵥ T)
  have hS : 0 ≤ ∑ s, ((tensorSlot s H *ᵥ T) ⬝ᵥ (tensorSlot s H *ᵥ T)) :=
    Finset.sum_nonneg fun s _ => dotProduct_self_nonnegative _
  unfold energyNoiseCorrection
  linarith

theorem sum_energyNoiseCorrection_lower_three_halves (T : (Fin r → Fin n) → ℝ)
    (H : Fin q → Matrix (Fin n) (Fin n) ℝ) (W : Fin q → (Fin r → Fin n) → ℝ)
    (hH : ∀ k, (H k).transpose = H k) (K : ℝ)
    (hK : (K • (1 : Matrix (Fin n) (Fin n) ℝ) - ∑ k, H k * H k).PosSemidef) :
    (1/2 : ℝ) * (∑ k, W k ⬝ᵥ W k) - (3/2 : ℝ)*K*(r : ℝ)^2*(T ⬝ᵥ T) ≤
      ∑ k, energyNoiseCorrection T (H k) (W k) := by
  have hb := tensorSlotSum_noise_sum_le H hH K hK T
  have hl := Finset.sum_le_sum (s := Finset.univ)
    (fun k _ => energyNoiseCorrection_lower_three_halves T (H k) (W k))
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at hl
  nlinarith

end KLS.TensorEnergy
namespace KLS.AdaptiveLocalization
open KLS.TensorEnergy
variable {n r : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

theorem cumulantEnergy_drift_lower_twelve (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (hr : 2 ≤ r)
    (u : Space n) (z : Fin (n+n*n) → ℝ)
    (hK : ((8 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) -
      ∑ k, whitenedCovarianceNoiseMatrix μ k z * whitenedCovarianceNoiseMatrix μ k z).PosSemidef) :
    (1/2 : ℝ) * cumulantEnergy μ (r+1) u z -
      (((r+2 : ℕ) : ℝ) + 12*(r : ℝ)^2) * cumulantEnergy μ r u z -
      2 * (whitenedCumulantTensor μ r u z ⬝ᵥ whitenedLowerCumulantTensor μ r u z) ≤
      differentialGenerator (coordinateDrift μ z) (fun k => coordinateDiffusion μ k z)
        (cumulantEnergy μ r u) z := by
  rw [cumulantEnergy_generator_exact hμ hfull hr u z]
  have h := sum_energyNoiseCorrection_lower_three_halves (whitenedCumulantTensor μ r u z)
    (fun k => whitenedCovarianceNoiseMatrix μ k z) (fun k => whitenedNextCumulantTensor μ r u k z)
    (fun k => (whitenedCovarianceNoiseMatrix_isSymm hμ z k).eq) 8 hK
  rw [← cumulantEnergy_eq_whitened hμ hfull, sum_whitenedNextCumulantTensor_square hμ hfull] at h
  nlinarith

end KLS.AdaptiveLocalization
end

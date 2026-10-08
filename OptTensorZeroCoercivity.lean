import OptTensorSlotCorrection

/-! The zero-coercivity energy estimate sharpens the compact cumulant
envelope separately from the integrated-energy envelope. -/
open Matrix MeasureTheory Set
open scoped BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS.TensorEnergy
variable {n r q : ℕ}

theorem two_dotProduct_le_one {ι : Type*} [Fintype ι] (v w : ι → ℝ) :
    2 * (v ⬝ᵥ w) ≤ (1 : ℝ) * (v ⬝ᵥ v) + (1 : ℝ) * (w ⬝ᵥ w) := by
  have h : ∑ i, (2 * (v i * w i)) ≤ ∑ i, ((1 : ℝ) * (v i * v i) + (1 : ℝ) * (w i * w i)) := by
    apply Finset.sum_le_sum
    intro i _
    nlinarith [sq_nonneg (v i - w i)]
  simpa only [dotProduct, Finset.sum_add_distrib, ← Finset.mul_sum] using h

theorem energyNoiseCorrection_lower_zeroCoercivity_slots
    (T : (Fin r → Fin n) → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (W : (Fin r → Fin n) → ℝ) :
    (0 : ℝ) * (W ⬝ᵥ W) - (((r : ℝ)-1)/2) *
      (∑ s, (tensorSlot s H *ᵥ T) ⬝ᵥ (tensorSlot s H *ᵥ T)) ≤
      energyNoiseCorrection T H W := by
  have hYoung := two_dotProduct_le_one W (tensorSlotSum H *ᵥ T)
  have hcs := dotProduct_sum_self_le (fun s : Fin r => tensorSlot s H *ᵥ T)
  have hs : (∑ s : Fin r, tensorSlot s H *ᵥ T) = tensorSlotSum H *ᵥ T := by
    simp only [tensorSlotSum, Matrix.sum_mulVec]
  rw [hs] at hcs
  unfold energyNoiseCorrection
  linarith

theorem sum_energyNoiseCorrection_lower_zeroCoercivity_slots (hr : 1 ≤ r)
    (T : (Fin r → Fin n) → ℝ)
    (H : Fin q → Matrix (Fin n) (Fin n) ℝ) (W : Fin q → (Fin r → Fin n) → ℝ)
    (hH : ∀ k, (H k).transpose = H k) (K : ℝ)
    (hK : (K • (1 : Matrix (Fin n) (Fin n) ℝ) - ∑ k, H k * H k).PosSemidef) :
    (0 : ℝ) * (∑ k, W k ⬝ᵥ W k) - (K/2)*(r : ℝ)*((r : ℝ)-1)*(T ⬝ᵥ T) ≤
      ∑ k, energyNoiseCorrection T (H k) (W k) := by
  have hb := tensorSlot_noise_double_sum_le H hH K hK T
  have hl := Finset.sum_le_sum (s := Finset.univ)
    (fun k _ => energyNoiseCorrection_lower_zeroCoercivity_slots T (H k) (W k))
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at hl
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hc := mul_le_mul_of_nonneg_left hb (show 0 ≤ ((r : ℝ)-1)/2 by linarith)
  nlinarith

end KLS.TensorEnergy
namespace KLS.AdaptiveLocalization
open KLS.TensorEnergy
variable {n r : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

theorem cumulantEnergy_drift_lower_zeroCoercivity (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (hr : 2 ≤ r)
    (u : Space n) (z : Fin (n+n*n) → ℝ)
    (hK : ((8 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) -
      ∑ k, whitenedCovarianceNoiseMatrix μ k z * whitenedCovarianceNoiseMatrix μ k z).PosSemidef) :
    (0 : ℝ) * cumulantEnergy μ (r+1) u z -
      (((r+2 : ℕ) : ℝ) + 4*(r : ℝ)*((r : ℝ)-1)) * cumulantEnergy μ r u z -
      2 * (whitenedCumulantTensor μ r u z ⬝ᵥ whitenedLowerCumulantTensor μ r u z) ≤
      differentialGenerator (coordinateDrift μ z) (fun k => coordinateDiffusion μ k z)
        (cumulantEnergy μ r u) z := by
  rw [cumulantEnergy_generator_exact hμ hfull hr u z]
  have h := sum_energyNoiseCorrection_lower_zeroCoercivity_slots (by omega : 1 ≤ r)
    (whitenedCumulantTensor μ r u z)
    (fun k => whitenedCovarianceNoiseMatrix μ k z) (fun k => whitenedNextCumulantTensor μ r u k z)
    (fun k => (whitenedCovarianceNoiseMatrix_isSymm hμ z k).eq) 8 hK
  rw [← cumulantEnergy_eq_whitened hμ hfull, sum_whitenedNextCumulantTensor_square hμ hfull] at h
  nlinarith

end KLS.AdaptiveLocalization
end

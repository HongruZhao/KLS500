import KLS.TensorEnergyCorrection

/-! The exact r² loss in lifting a matrix noise bound to r tensor slots. -/
open Matrix
open scoped BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS.TensorEnergy
variable {n r q : ℕ}

theorem dotProduct_sum_self_le {ι : Type*} [Fintype ι] (V : Fin r → ι → ℝ) :
    (∑ s, V s) ⬝ᵥ (∑ s, V s) ≤ (r : ℝ) * ∑ s, V s ⬝ᵥ V s := by
  have hh : (∑ a : ι, (∑ s, V s a)^2) ≤ ∑ a : ι, (r : ℝ) * ∑ s, (V s a)^2 := by
    apply Finset.sum_le_sum
    intro a _
    simpa using (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun s : Fin r => V s a))
  simp only [← Finset.mul_sum] at hh
  rw [Finset.sum_comm] at hh
  simpa only [dotProduct, Finset.sum_apply, pow_two] using hh

/-- Paper (91), with its matrix-order hypothesis displayed explicitly. -/
theorem tensorSlotSum_noise_sum_le (H : Fin q → Matrix (Fin n) (Fin n) ℝ)
    (hH : ∀ k, (H k).transpose = H k) (K : ℝ)
    (hK : (K • (1 : Matrix (Fin n) (Fin n) ℝ) - ∑ k, H k * H k).PosSemidef)
    (T : (Fin r → Fin n) → ℝ) :
    (∑ k, (tensorSlotSum (H k) *ᵥ T) ⬝ᵥ (tensorSlotSum (H k) *ᵥ T)) ≤
      K * (r : ℝ)^2 * (T ⬝ᵥ T) := by
  have hcs : (∑ k, (tensorSlotSum (H k) *ᵥ T) ⬝ᵥ (tensorSlotSum (H k) *ᵥ T)) ≤
      ∑ k, (r : ℝ) * ∑ s, (tensorSlot s (H k) *ᵥ T) ⬝ᵥ (tensorSlot s (H k) *ᵥ T) := by
    apply Finset.sum_le_sum
    intro k _
    simpa only [tensorSlotSum, Matrix.sum_mulVec] using
      dotProduct_sum_self_le (fun s : Fin r => tensorSlot s (H k) *ᵥ T)
  have hslots : (∑ s : Fin r, ∑ k, (tensorSlot s (H k) *ᵥ T) ⬝ᵥ (tensorSlot s (H k) *ᵥ T)) ≤
      ∑ _s : Fin r, K * (T ⬝ᵥ T) :=
    Finset.sum_le_sum fun s _ => tensorSlot_noise_sum_le H hH K hK s T
  rw [← Finset.mul_sum, Finset.sum_comm] at hcs
  calc
    _ ≤ (r : ℝ) * ∑ s : Fin r, ∑ k, (tensorSlot s (H k) *ᵥ T) ⬝ᵥ (tensorSlot s (H k) *ᵥ T) := hcs
    _ ≤ (r : ℝ) * ∑ _s : Fin r, K * (T ⬝ᵥ T) :=
      mul_le_mul_of_nonneg_left hslots (Nat.cast_nonneg r)
    _ = _ := by simp; ring

theorem sum_energyNoiseCorrection_lower (T : (Fin r → Fin n) → ℝ)
    (H : Fin q → Matrix (Fin n) (Fin n) ℝ) (W : Fin q → (Fin r → Fin n) → ℝ)
    (hH : ∀ k, (H k).transpose = H k) (K : ℝ)
    (hK : (K • (1 : Matrix (Fin n) (Fin n) ℝ) - ∑ k, H k * H k).PosSemidef) :
    (1/2 : ℝ) * (∑ k, W k ⬝ᵥ W k) - 2*K*(r : ℝ)^2*(T ⬝ᵥ T) ≤
      ∑ k, energyNoiseCorrection T (H k) (W k) := by
  have hb := tensorSlotSum_noise_sum_le H hH K hK T
  have hl := Finset.sum_le_sum (s := Finset.univ)
    (fun k _ => energyNoiseCorrection_lower T (H k) (W k))
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at hl
  nlinarith

end KLS.TensorEnergy
end
#print axioms KLS.TensorEnergy.tensorSlotSum_noise_sum_le
#print axioms KLS.TensorEnergy.sum_energyNoiseCorrection_lower

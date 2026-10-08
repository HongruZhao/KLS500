import KLS.TensorMetricGenerator
import KLS.PositiveMatrixSquareRoot

/-! Exact finite-dimensional estimates for the energy noise correction.
The matrix seed bound is an explicit hypothesis, not an assumed universal result. -/
open Matrix
open scoped BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS.TensorEnergy
variable {n r q : ℕ}

def energyNoiseCorrection (T : (Fin r → Fin n) → ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (W : (Fin r → Fin n) → ℝ) : ℝ :=
  W ⬝ᵥ W - 2 * (W ⬝ᵥ (tensorSlotSum H *ᵥ T)) +
    (1/2 : ℝ) * ((tensorSlotSum H *ᵥ T) ⬝ᵥ (tensorSlotSum H *ᵥ T)) +
    (1/2 : ℝ) * ∑ s, ((tensorSlot s H *ᵥ T) ⬝ᵥ (tensorSlot s H *ᵥ T))

theorem dotProduct_self_nonnegative {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    0 ≤ v ⬝ᵥ v := Finset.sum_nonneg fun i _ => mul_self_nonneg _

theorem two_dotProduct_le {ι : Type*} [Fintype ι] (v w : ι → ℝ) :
    2 * (v ⬝ᵥ w) ≤ (1/2 : ℝ) * (v ⬝ᵥ v) + 2 * (w ⬝ᵥ w) := by
  have h : ∑ i, (2 * (v i * w i)) ≤ ∑ i, ((1/2 : ℝ) * (v i * v i) + 2 * (w i * w i)) := by
    apply Finset.sum_le_sum
    intro i _
    nlinarith [sq_nonneg (v i - 2*w i)]
  simpa only [dotProduct, Finset.sum_add_distrib, ← Finset.mul_sum] using h

theorem energyNoiseCorrection_lower (T : (Fin r → Fin n) → ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (W : (Fin r → Fin n) → ℝ) :
    (1/2 : ℝ) * (W ⬝ᵥ W) - 2 * ((tensorSlotSum H *ᵥ T) ⬝ᵥ (tensorSlotSum H *ᵥ T)) ≤
      energyNoiseCorrection T H W := by
  have hYoung := two_dotProduct_le W (tensorSlotSum H *ᵥ T)
  have hV := dotProduct_self_nonnegative (tensorSlotSum H *ᵥ T)
  have hS : 0 ≤ ∑ s, ((tensorSlot s H *ᵥ T) ⬝ᵥ (tensorSlot s H *ᵥ T)) :=
    Finset.sum_nonneg fun s _ => dotProduct_self_nonnegative _
  unfold energyNoiseCorrection
  linarith

theorem tensorSlot_posSemidef (s : Fin r) {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : B.PosSemidef) : (tensorSlot s B).PosSemidef := by
  obtain ⟨R, _, hR⟩ := KLS.exists_symmetric_matrix_square_root hB
  rw [← hR, tensorSlot_mul, ← tensorSlot_transpose]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_conjTranspose_mul_self (tensorSlot s R)

theorem tensorSlot_sum (s : Fin r) (M : Fin q → Matrix (Fin n) (Fin n) ℝ) :
    tensorSlot s (∑ k, M k) = ∑ k, tensorSlot s (M k) := by
  classical
  have h : ∀ S : Finset (Fin q), tensorSlot s (∑ k ∈ S, M k) = ∑ k ∈ S, tensorSlot s (M k) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp [tensorSlot_zero]
    | @insert k S hk ih => simp [hk, tensorSlot_add, ih]
  exact h Finset.univ

/-- A true matrix-order bound lifts to each tensor slot. -/
theorem tensorSlot_noise_sum_le (H : Fin q → Matrix (Fin n) (Fin n) ℝ)
    (hH : ∀ k, (H k).transpose = H k) (K : ℝ)
    (hK : (K • (1 : Matrix (Fin n) (Fin n) ℝ) - ∑ k, H k * H k).PosSemidef)
    (s : Fin r) (T : (Fin r → Fin n) → ℝ) :
    (∑ k, (tensorSlot s (H k) *ᵥ T) ⬝ᵥ (tensorSlot s (H k) *ᵥ T)) ≤ K * (T ⬝ᵥ T) := by
  have hp := (tensorSlot_posSemidef s hK).dotProduct_mulVec_nonneg T
  simp only [Pi.star_apply, star_trivial] at hp
  rw [tensorSlot_sub, tensorSlot_smul, tensorSlot_one, tensorSlot_sum] at hp
  simp only [tensorSlot_mul, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    Matrix.sum_mulVec, dotProduct_sub, dotProduct_smul, dotProduct_sum, smul_eq_mul] at hp
  have hSq (k : Fin q) := dotProduct_matrix_square (tensorSlot s (H k))
    (by rw [tensorSlot_transpose, hH k]) T
  simp_rw [hSq] at hp
  linarith

end KLS.TensorEnergy
end
#print axioms KLS.TensorEnergy.tensorSlot_noise_sum_le

import OptCumulantTensorSymmetry
import OptSymmetricCollectiveBound
import OptTensorYoungParameter

open Matrix MeasureTheory Set
open scoped BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS.TensorEnergy
variable {n r q : ℕ}

theorem energyNoiseCorrection_lower_young_collective (hr : 1 ≤ r) (η : ℝ) (hη : 1 ≤ η)
    (T : (Fin r → Fin n) → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (W : (Fin r → Fin n) → ℝ) :
    (1-η⁻¹)*(W ⬝ᵥ W) - (((2*η-1)*(r : ℝ)-1)/(2*r))*
      ((tensorSlotSum H *ᵥ T) ⬝ᵥ (tensorSlotSum H *ᵥ T)) ≤ energyNoiseCorrection T H W := by
  have hYoung := two_dotProduct_le_parameter η (by linarith) W (tensorSlotSum H *ᵥ T)
  have hcs := dotProduct_sum_self_le (fun s : Fin r => tensorSlot s H *ᵥ T)
  have hs : (∑ s : Fin r, tensorSlot s H *ᵥ T) = tensorSlotSum H *ᵥ T := by
    simp only [tensorSlotSum, Matrix.sum_mulVec]
  rw [hs] at hcs
  have hr' : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hd : ((tensorSlotSum H *ᵥ T) ⬝ᵥ (tensorSlotSum H *ᵥ T))/(r : ℝ) ≤
      ∑ s, (tensorSlot s H *ᵥ T) ⬝ᵥ (tensorSlot s H *ᵥ T) := (div_le_iff₀ hr').mpr (by nlinarith [hcs])
  have he : (((2*η-1)*(r : ℝ)-1)/(2*r)) = η-1/2-1/(2*r) := by field_simp
  have hd2 : (1/(2*(r : ℝ)))*((tensorSlotSum H *ᵥ T) ⬝ᵥ (tensorSlotSum H *ᵥ T)) ≤
      (1/2 : ℝ)*∑ s, (tensorSlot s H *ᵥ T) ⬝ᵥ (tensorSlot s H *ᵥ T) := by
    rw [one_div_mul_eq_div]
    apply (div_le_iff₀ (show 0 < 2*(r : ℝ) by positivity)).mpr
    nlinarith [hcs]
  rw [he]
  unfold energyNoiseCorrection
  nlinarith [hd2]

theorem sum_energyNoiseCorrection_lower_symmetric_young (hr : 2 ≤ r) (η : ℝ) (hη : 1 ≤ η)
    (T : (Fin r → Fin n) → ℝ)
    (H : Fin q → Matrix (Fin n) (Fin n) ℝ) (W : Fin q → (Fin r → Fin n) → ℝ)
    (hB : (∑ k, (tensorSlotSum (H k) *ᵥ T) ⬝ᵥ (tensorSlotSum (H k) *ᵥ T)) ≤
      (4*(r : ℝ)^2+8*r)*(T ⬝ᵥ T)) :
    (1-η⁻¹)*(∑ k, W k ⬝ᵥ W k) -
      ((4*η-2)*(r : ℝ)^2+(8*η-6)*r-4)*(T ⬝ᵥ T) ≤
      ∑ k, energyNoiseCorrection T (H k) (W k) := by
  have hl := Finset.sum_le_sum (s := Finset.univ)
    (fun k _ => energyNoiseCorrection_lower_young_collective (by omega : 1 ≤ r) η hη T (H k) (W k))
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at hl
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hrpos : (0 : ℝ) < r := by linarith
  have hcoef : 0 ≤ ((2*η-1)*(r : ℝ)-1)/(2*r) := by
    apply div_nonneg _ (by positivity)
    nlinarith [mul_nonneg (show 0 ≤ η-1 by linarith) (Nat.cast_nonneg (α := ℝ) r)]
  have hb := mul_le_mul_of_nonneg_left hB hcoef
  have he : (((2*η-1)*(r : ℝ)-1)/(2*r))*(4*(r : ℝ)^2+8*r) =
      (4*η-2)*(r : ℝ)^2+(8*η-6)*r-4 := by field_simp; ring
  rw [← mul_assoc, he] at hb
  linarith

theorem matrix_noise_unit_norm_le (H : Fin q → Matrix (Fin n) (Fin n) ℝ)
    (hH : ∀ k, (H k).transpose = H k) (K : ℝ)
    (hK : (K • (1 : Matrix (Fin n) (Fin n) ℝ) - ∑ k, H k*H k).PosSemidef)
    (x : Space n) (hx : ‖x‖ = 1) :
    ∑ k, ‖(H k).toEuclideanLin x‖^2 ≤ K := by
  have hp := hK.dotProduct_mulVec_nonneg x.ofLp
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, Matrix.sum_mulVec, dotProduct_sub, dotProduct_smul,
    dotProduct_sum, smul_eq_mul] at hp
  simp_rw [dotProduct_matrix_square _ (hH _)] at hp
  have hn : x.ofLp ⬝ᵥ x.ofLp = 1 := by rw [← norm_sq_eq_dotProduct, hx]; norm_num
  rw [hn, mul_one] at hp
  simp only [norm_sq_eq_dotProduct]
  change (∑ k, (H k *ᵥ x.ofLp) ⬝ᵥ (H k *ᵥ x.ofLp)) ≤ K
  linarith

end KLS.TensorEnergy
namespace KLS.AdaptiveLocalization
open KLS.TensorEnergy
variable {n r : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

theorem cumulantEnergy_drift_lower_symmetric_young (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (hr : 2 ≤ r) (η : ℝ) (hη : 1 ≤ η)
    (u : Space n) (z : Fin (n+n*n) → ℝ)
    (hK : ((8 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) -
      ∑ k, whitenedCovarianceNoiseMatrix μ k z * whitenedCovarianceNoiseMatrix μ k z).PosSemidef)
    (h4 : ∀ x : Space n, ‖x‖ = 1 →
      ∑ k, (inner ℝ x ((whitenedCovarianceNoiseMatrix μ k z).toEuclideanLin x))^2 ≤ 4) :
    (1-η⁻¹)*cumulantEnergy μ (r+1) u z -
      ((4*η-2)*(r : ℝ)^2+(8*η-5)*r-2)*cumulantEnergy μ r u z -
      2*(whitenedCumulantTensor μ r u z ⬝ᵥ whitenedLowerCumulantTensor μ r u z) ≤
      differentialGenerator (coordinateDrift μ z) (fun k => coordinateDiffusion μ k z)
        (cumulantEnergy μ r u) z := by
  rw [cumulantEnergy_generator_exact hμ hfull hr u z]
  have hH := fun k => (whitenedCovarianceNoiseMatrix_isSymm hμ z k).eq
  have hB := tensorSlotSum_noise_sum_le_symmetric hr
    (fun k => whitenedCovarianceNoiseMatrix μ k z) hH 8 4
    (matrix_noise_unit_norm_le _ hH 8 hK) h4
    (whitenedCumulantTensor μ r u z) (whitenedCumulantTensor_symmetric hμ u z)
  have hBeq : 2*(r : ℝ)*8+r*(r-2)*4 = 4*(r : ℝ)^2+8*r := by ring
  rw [hBeq] at hB
  have h := sum_energyNoiseCorrection_lower_symmetric_young hr η hη
    (whitenedCumulantTensor μ r u z) (fun k => whitenedCovarianceNoiseMatrix μ k z)
    (fun k => whitenedNextCumulantTensor μ r u k z) hB
  rw [← cumulantEnergy_eq_whitened hμ hfull, sum_whitenedNextCumulantTensor_square hμ hfull] at h
  push_cast
  nlinarith

end KLS.AdaptiveLocalization
end

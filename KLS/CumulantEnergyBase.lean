import KLS.CumulantRankOne

/-! The actual second and third cumulant energies satisfy the base inequality
under the literal normalized covariance-noise matrix bound. -/
open MeasureTheory ProbabilityTheory Matrix Set
open scoped BigOperators Matrix.Norms.Elementwise Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS.AdaptiveLocalization
open KLS.TensorEnergy
variable {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

theorem cumulantEnergy_one_eq_covariance (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (u : Space n) (z : Fin (n+n*n) → ℝ) :
    cumulantEnergy μ 1 u z = inner ℝ u (matrixAction (coordinateCovarianceMatrix μ z) u) := by
  unfold cumulantEnergy tensorMetric
  rw [coordinateCumulantTensor_one hμ, tensorMatrix_rankOne, rankOneTensor_dot,
    Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _
      (isUnit_iff_ne_zero.mpr (coordinateCovarianceMatrix_posDef hμ hfull z).det_pos.ne'),
    Matrix.one_mulVec]
  simp only [dotProduct, inner_eq_coordinate_sum, matrixAction_apply, Matrix.mulVec]

theorem cumulantEnergy_one_zero (hμ : IsCompact μ.support)
    (hiso : IsIsotropic μ) (u : Space n) : cumulantEnergy μ 1 u 0 = ‖u‖^2 := by
  rw [cumulantEnergy_one_eq_covariance hμ hiso.affineSpan_support_eq_top,
    ← directionalCovarianceCLM_apply]
  simpa only [coordinateCovarianceMatrix, decodeState_zero, Prod.fst_zero, Prod.snd_zero,
    covariance_zero_zero_eq_one hiso] using directionalCovarianceCLM_one u

theorem whitenedNextCumulantTensor_one_eq_slot (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤)
    (u : Space n) (z : Fin (n+n*n) → ℝ) (k : Fin n) :
    whitenedNextCumulantTensor μ 1 u k z =
      tensorSlot (0 : Fin 1) (whitenedCovarianceNoiseMatrix μ k z) *ᵥ
        whitenedCumulantTensor μ 1 u z := by
  let P := inverseSqrtCovariance μ (decodeState z)
  let A := coordinateCovarianceMatrix μ z
  have hp : IsUnit P.det := isUnit_iff_ne_zero.mpr (inverseSqrtCovariance_det_ne_zero hμ hfull _)
  have hwhite : P * A * P = 1 := by
    simpa only [P, A, coordinateCovarianceMatrix,
      (inverseSqrtCovariance_isSymm (μ := μ) (decodeState z)).eq] using
      inverseSqrtCovariance_whitens hμ hfull (decodeState z)
  have hPA : P * A = P⁻¹ := by
    calc
      _ = P * (P⁻¹ * P⁻¹) := by rw [inverse_whitener_square hwhite]
      _ = _ := by rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hp, Matrix.one_mul]
  have hPPA : P * P * A = 1 := by
    rw [Matrix.mul_assoc, hPA, Matrix.mul_nonsing_inv _ hp]
  rw [whitenedNextCumulantTensor_one hμ, whitenedCumulantTensor_one hμ,
    tensorSlot_rankOne]
  congr 1
  change P *ᵥ (covarianceNoiseMatrix μ k z *ᵥ u.ofLp) =
    (P * covarianceNoiseMatrix μ k z * P) *ᵥ (P *ᵥ (A *ᵥ u.ofLp))
  simp only [Matrix.mulVec_mulVec]
  congr 1
  calc
    P * covarianceNoiseMatrix μ k z = P * covarianceNoiseMatrix μ k z * (P * P * A) := by rw [hPPA, Matrix.mul_one]
    _ = _ := by simp only [Matrix.mul_assoc]

/-- The normalized matrix bound controls the literal next energy, including
all coordinate contractions and inverse-covariance weights. -/
theorem cumulantEnergy_two_le_eight_covariance (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤)
    (u : Space n) (z : Fin (n+n*n) → ℝ)
    (hseed : ((8 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) -
      ∑ k, whitenedCovarianceNoiseMatrix μ k z * whitenedCovarianceNoiseMatrix μ k z).PosSemidef) :
    cumulantEnergy μ 2 u z ≤ 8 * inner ℝ u (matrixAction (coordinateCovarianceMatrix μ z) u) := by
  have hb := tensorSlot_noise_sum_le (fun k => whitenedCovarianceNoiseMatrix μ k z)
    (fun k => (whitenedCovarianceNoiseMatrix_isSymm hμ z k).eq) 8 hseed
    (0 : Fin 1) (whitenedCumulantTensor μ 1 u z)
  simp_rw [← whitenedNextCumulantTensor_one_eq_slot hμ hfull] at hb
  rw [sum_whitenedNextCumulantTensor_square hμ hfull,
    ← cumulantEnergy_eq_whitened hμ hfull, cumulantEnergy_one_eq_covariance hμ hfull] at hb
  exact hb

end KLS.AdaptiveLocalization
end

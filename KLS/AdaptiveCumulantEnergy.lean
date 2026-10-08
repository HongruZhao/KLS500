import KLS.AdaptiveCumulantTensor
import KLS.TensorSlotSumBound

/-! The literal cumulant-energy observable and its exact actual localization
generator. Matrix and cumulant drift hypotheses are discharged here. -/
open MeasureTheory ProbabilityTheory Matrix Set
open scoped BigOperators Matrix.Norms.Elementwise Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS.AdaptiveLocalization
open KLS.TensorEnergy
variable {n r : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

def cumulantEnergy (μ : Measure (Space n)) (r : ℕ) (u : Space n)
    (z : Fin (n+n*n) → ℝ) : ℝ :=
  tensorMetric (coordinateCovarianceMatrix μ z) (coordinateCumulantTensor μ r u z)

def whitenedCumulantTensor (μ : Measure (Space n)) (r : ℕ) (u : Space n)
    (z : Fin (n+n*n) → ℝ) : (Fin r → Fin n) → ℝ :=
  tensorMatrix (inverseSqrtCovariance μ (decodeState z)) *ᵥ coordinateCumulantTensor μ r u z

def whitenedLowerCumulantTensor (μ : Measure (Space n)) (r : ℕ) (u : Space n)
    (z : Fin (n+n*n) → ℝ) : (Fin r → Fin n) → ℝ :=
  tensorMatrix (inverseSqrtCovariance μ (decodeState z)) *ᵥ lowerCumulantTensor μ r u z

def whitenedNextCumulantTensor (μ : Measure (Space n)) (r : ℕ) (u : Space n)
    (k : Fin n) (z : Fin (n+n*n) → ℝ) : (Fin r → Fin n) → ℝ :=
  tensorMatrix (inverseSqrtCovariance μ (decodeState z)) *ᵥ nextCumulantTensor μ r u k z

theorem inverseSqrtCovariance_det_ne_zero (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (p : Parameter n) :
    (inverseSqrtCovariance μ p).det ≠ 0 := by
  intro hz
  have hh := congrArg Matrix.det (inverseSqrtCovariance_whitens hμ hfull p)
  simp only [Matrix.det_mul, hz, zero_mul, Matrix.det_one] at hh
  exact zero_ne_one hh

theorem covarianceNoiseMatrix_transpose (hμ : IsCompact μ.support)
    (z : Fin (n+n*n) → ℝ) (k : Fin n) :
    (covarianceNoiseMatrix μ k z).transpose = covarianceNoiseMatrix μ k z := by
  ext i j
  simp only [Matrix.transpose_apply, covarianceNoiseMatrix_eq_integral hμ]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

theorem cumulantEnergy_eq_whitened (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (u : Space n) (z : Fin (n+n*n) → ℝ) :
    cumulantEnergy μ r u z = whitenedCumulantTensor μ r u z ⬝ᵥ whitenedCumulantTensor μ r u z := by
  apply tensorMetric_eq_whitened (coordinateCovarianceMatrix μ z)
    (inverseSqrtCovariance μ (decodeState z)) (inverseSqrtCovariance_isSymm _).eq
    (inverseSqrtCovariance_det_ne_zero hμ hfull _)
  simpa only [coordinateCovarianceMatrix, (inverseSqrtCovariance_isSymm (μ := μ) (decodeState z)).eq] using
    inverseSqrtCovariance_whitens hμ hfull (decodeState z)

theorem cumulantEnergy_nonnegative (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (u : Space n) (z : Fin (n+n*n) → ℝ) :
    0 ≤ cumulantEnergy μ r u z := by
  rw [cumulantEnergy_eq_whitened hμ hfull]
  exact dotProduct_self_nonnegative _

theorem contDiff_cumulantEnergy (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (u : Space n) :
    ContDiff ℝ (⊤ : ℕ∞) (cumulantEnergy μ r u) :=
  contDiff_tensorMetric (contDiff_coordinateCovarianceMatrix hμ)
    (fun z => (coordinateCovarianceMatrix_posDef hμ hfull z).det_pos.ne')
    (contDiff_coordinateCumulantTensor hμ u)

/-- Literal equation (89) for the actual current-law cumulant energy. -/
theorem cumulantEnergy_generator_exact (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (hr : 2 ≤ r)
    (u : Space n) (z : Fin (n+n*n) → ℝ) :
    differentialGenerator (coordinateDrift μ z) (fun k => coordinateDiffusion μ k z)
      (cumulantEnergy μ r u) z =
      -((r+2 : ℕ) : ℝ) * cumulantEnergy μ r u z -
      2 * (whitenedCumulantTensor μ r u z ⬝ᵥ whitenedLowerCumulantTensor μ r u z) +
      ∑ k, energyNoiseCorrection (whitenedCumulantTensor μ r u z)
        (whitenedCovarianceNoiseMatrix μ k z) (whitenedNextCumulantTensor μ r u k z) := by
  let P := inverseSqrtCovariance μ (decodeState z)
  have hPs : P.transpose = P := (inverseSqrtCovariance_isSymm _).eq
  have hwhite : P * coordinateCovarianceMatrix μ z * P = 1 := by
    simpa only [P, coordinateCovarianceMatrix,
      (inverseSqrtCovariance_isSymm (μ := μ) (decodeState z)).eq] using
      inverseSqrtCovariance_whitens hμ hfull (decodeState z)
  have hH (k : Fin n) : (fderiv ℝ (coordinateCovarianceMatrix μ) z (coordinateDiffusion μ k z)).transpose =
      fderiv ℝ (coordinateCovarianceMatrix μ) z (coordinateDiffusion μ k z) := by
    rw [fderiv_coordinateCovarianceMatrix_diffusion hμ]
    exact covarianceNoiseMatrix_transpose hμ z k
  have hh := differentialGenerator_tensorMetric_whitened
    (contDiff_coordinateCovarianceMatrix hμ)
    (fun z => (coordinateCovarianceMatrix_posDef hμ hfull z).det_pos.ne')
    (contDiff_coordinateCumulantTensor (r := r) hμ u) (coordinateDrift μ z)
    (fun k => coordinateDiffusion μ k z) z P hPs
    (inverseSqrtCovariance_det_ne_zero hμ hfull _) hwhite hH
    ((r+1 : ℕ) : ℝ) (lowerCumulantTensor μ r u z)
    (coordinateCovarianceMatrix_generator hμ hfull z)
    (coordinateCumulantTensor_generator hμ hfull hr u z)
  simp_rw [fderiv_coordinateCovarianceMatrix_diffusion hμ,
    fderiv_coordinateCumulantTensor_diffusion hμ] at hh
  have hcoef : (r : ℝ) - 2*((r+1 : ℕ) : ℝ) = -((r+2 : ℕ) : ℝ) := by push_cast; ring
  rw [hcoef] at hh
  rw [cumulantEnergy_eq_whitened hμ hfull]
  exact hh

/-- The universal matrix seed is explicitly isolated as hK; it has not been
assumed as part of the process or cumulant dynamics. -/
theorem cumulantEnergy_generator_lower_of_matrix_seed (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (hr : 2 ≤ r)
    (u : Space n) (z : Fin (n+n*n) → ℝ) (K : ℝ)
    (hK : (K • (1 : Matrix (Fin n) (Fin n) ℝ) -
      ∑ k, whitenedCovarianceNoiseMatrix μ k z * whitenedCovarianceNoiseMatrix μ k z).PosSemidef) :
    (1/2 : ℝ) * (∑ k, whitenedNextCumulantTensor μ r u k z ⬝ᵥ whitenedNextCumulantTensor μ r u k z) -
      (((r+2 : ℕ) : ℝ) + 2*K*(r : ℝ)^2) * cumulantEnergy μ r u z -
      2 * (whitenedCumulantTensor μ r u z ⬝ᵥ whitenedLowerCumulantTensor μ r u z) ≤
      differentialGenerator (coordinateDrift μ z) (fun k => coordinateDiffusion μ k z)
        (cumulantEnergy μ r u) z := by
  rw [cumulantEnergy_generator_exact hμ hfull hr u z]
  have h := sum_energyNoiseCorrection_lower (whitenedCumulantTensor μ r u z)
    (fun k => whitenedCovarianceNoiseMatrix μ k z) (fun k => whitenedNextCumulantTensor μ r u k z)
    (fun k => (whitenedCovarianceNoiseMatrix_isSymm hμ z k).eq) K hK
  rw [← cumulantEnergy_eq_whitened hμ hfull] at h
  nlinarith

end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.cumulantEnergy_generator_exact
#print axioms KLS.AdaptiveLocalization.cumulantEnergy_generator_lower_of_matrix_seed

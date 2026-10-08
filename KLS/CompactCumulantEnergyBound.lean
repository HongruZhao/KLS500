import KLS.LowerCumulantSubsetSum

/-! Transport of the smaller-order compact isotropic cumulant bound to
the actual current law. This is (100), with the covariance factor kept. -/
open MeasureTheory Set Matrix
open scoped BigOperators Matrix.Norms.Elementwise
noncomputable section
namespace KLS

def CompactCumulantEnergyBound (n r : ℕ) (B : ℝ) : Prop :=
  ∀ ν : Measure (Space n), IsCompact ν.support → admissibleMeasure ν → ∀ u : Space n,
    (∑ a : Fin r → Fin n, cumulantTensor ν (r+1)
      (Fin.cons u (fun s => EuclideanSpace.single (a s) (1 : ℝ))) ^ 2) ≤ B * ‖u‖^2

end KLS
namespace KLS.AdaptiveLocalization
open KLS.TensorEnergy
variable {n r : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

theorem cumulantEnergy_le_of_compactBound (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (hr : 1 ≤ r)
    (u : Space n) (z : Fin (n+n*n) → ℝ)
    (hlc : measureLogConcave (law μ (decodeState z).1 (decodeState z).2)) {B : ℝ}
    (hB : CompactCumulantEnergyBound n r B) :
    cumulantEnergy μ r u z ≤ B * inner ℝ u (matrixAction (coordinateCovarianceMatrix μ z) u) := by
  let ν := law μ (decodeState z).1 (decodeState z).2
  let := law_isProbability hμ (decodeState z).1 (decodeState z).2
  have hν : IsCompact ν.support := by dsimp [ν]; rwa [support_law hμ]
  have hp : (covarianceMatrix ν).PosDef := by
    rw [← covariance_eq_covarianceMatrix hμ]
    exact covariance_posDef hμ hfull _
  let P := inverseSqrtMatrix (covarianceMatrix ν)
  have hPs : P.transpose = P := (inverseSqrtMatrix_isSymm _).eq
  have hwhite : P * covarianceMatrix ν * P = 1 := by
    simpa only [P, (inverseSqrtMatrix_isSymm (covarianceMatrix ν)).eq] using
      inverseSqrtMatrix_mul_self_mul_transpose hp
  have hadm : admissibleMeasure (whitenedMeasure ν) :=
    ⟨inferInstance, hlc.whitenedMeasure, whitenedMeasure_isIsotropic hlc.memLp_id hp⟩
  have hh := hB _ (isCompact_support_whitenedMeasure hν) hadm (matrixAction P⁻¹ u)
  rw [norm_inverse_whitener_sq hPs hwhite] at hh
  rw [cumulantEnergy_eq_whitened hμ hfull]
  unfold dotProduct
  simp_rw [← pow_two, whitenedCumulantTensor_eq_evaluation]
  have he (a : Fin r → Fin n) :
      cumulantTensor ν (r+1) (Fin.cons u (fun s => inverseSqrtDirection μ z (a s))) =
        cumulantTensor (whitenedMeasure ν) (r+1)
          (Fin.cons (matrixAction P⁻¹ u) (fun s => EuclideanSpace.single (a s) (1 : ℝ))) := by
    simpa only [ν, matrixAction_inverseSqrt_single hμ, P] using
      cumulantTensor_whitened_evaluation hν hr hp u a
  simp_rw [← he] at hh
  simpa only [ν, ← covariance_eq_covarianceMatrix hμ, coordinateCovarianceMatrix] using hh

end KLS.AdaptiveLocalization
end

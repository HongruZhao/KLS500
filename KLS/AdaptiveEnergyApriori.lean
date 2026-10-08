import KLS.CumulantWhitening

/-! The actual adaptive cumulant energy has a dimension-dependent a priori
bound by its distinguished direction's actual covariance. -/
open MeasureTheory Set Filter Matrix
open scoped Topology ContDiff BigOperators Matrix.Norms.Elementwise
noncomputable section
namespace KLS.AdaptiveLocalization
open KLS.TensorEnergy
variable {n r : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

def energyAprioriConstant (n r : ℕ) : ℝ :=
  (n : ℝ)^r * cumulantAprioriConstant n (r+1)^2

theorem energyAprioriConstant_nonnegative (n r : ℕ) : 0 ≤ energyAprioriConstant n r := by
  unfold energyAprioriConstant
  positivity

theorem matrixAction_inverseSqrt_single (hμ : IsCompact μ.support)
    (z : Fin (n+n*n) → ℝ) (k : Fin n) :
    matrixAction (inverseSqrtMatrix (covarianceMatrix
      (law μ (decodeState z).1 (decodeState z).2))) (EuclideanSpace.single k 1) =
        inverseSqrtDirection μ z k := by
  rw [← covariance_eq_covarianceMatrix hμ]
  apply PiLp.ext
  intro j
  simp [matrixAction_apply, inverseSqrtDirection, inverseSqrtCovariance]

theorem cumulantEnergy_le_apriori_covariance (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (hr : 1 ≤ r)
    (u : Space n) (z : Fin (n+n*n) → ℝ)
    (hlc : measureLogConcave (law μ (decodeState z).1 (decodeState z).2)) :
    cumulantEnergy μ r u z ≤ energyAprioriConstant n r *
      inner ℝ u (matrixAction (coordinateCovarianceMatrix μ z) u) := by
  let ν := law μ (decodeState z).1 (decodeState z).2
  letI := law_isProbability hμ (decodeState z).1 (decodeState z).2
  have hv : IsCompact ν.support := by dsimp [ν]; rwa [support_law hμ]
  have hp : (covarianceMatrix ν).PosDef := by
    rw [← covariance_eq_covarianceMatrix hμ]
    exact covariance_posDef hμ hfull _
  rw [cumulantEnergy_eq_whitened hμ hfull]
  unfold dotProduct
  simp_rw [← pow_two, whitenedCumulantTensor_eq_evaluation]
  calc
    _ ≤ ∑ _a : Fin r → Fin n, cumulantAprioriConstant n (r+1)^2 *
        inner ℝ u (matrixAction (covarianceMatrix ν) u) := by
      apply Finset.sum_le_sum
      intro a _
      have hb := sq_cumulantTensor_whitened_le hv hlc hr hp u a
      simpa only [ν, matrixAction_inverseSqrt_single hμ] using hb
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_pow, ← covariance_eq_covarianceMatrix hμ,
        coordinateCovarianceMatrix, energyAprioriConstant, ν]
      ring

end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.cumulantEnergy_le_apriori_covariance

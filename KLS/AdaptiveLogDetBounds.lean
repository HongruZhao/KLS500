import KLS.AdaptiveWhitenedCovarianceNoise

/-! Dimension-dependent, parameter-uniform logdet coefficient bounds from actual log-concave moments. -/
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped Topology BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
namespace KLS.AdaptiveLocalization
variable {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

def normalizedThirdMomentBound (n : ℕ) : ℝ :=
  isotropicTailRadius n ^ 3 * geometricNormMomentConstant 3

theorem normalizedThirdMomentBound_pos (n : ℕ) : 0 < normalizedThirdMomentBound n :=
  mul_pos (pow_pos (isotropicTailRadius_pos n) _) (geometricNormMomentConstant_pos 3)

theorem whitenedCovarianceNoiseMatrix_isSymm (hμ : IsCompact μ.support)
    (z : Fin (n+n*n) → ℝ) (k : Fin n) : (whitenedCovarianceNoiseMatrix μ k z).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, whitenedCovarianceNoiseMatrix_eq_integral hμ]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

theorem abs_whitenedCovarianceNoiseMatrix_le (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (z : Fin (n+n*n) → ℝ)
    (hlc : measureLogConcave (law μ (decodeState z).1 (decodeState z).2)) (i j k : Fin n) :
    |whitenedCovarianceNoiseMatrix μ k z i j| ≤ normalizedThirdMomentBound n := by
  letI := law_isProbability hμ (decodeState z).1 (decodeState z).2
  have hp : (covarianceMatrix (law μ (decodeState z).1 (decodeState z).2)).PosDef := by
    rw [← covariance_eq_covarianceMatrix hμ (decodeState z)]
    exact covariance_posDef hμ hfull _
  rw [whitenedCovarianceNoiseMatrix_eq_integral hμ]
  simpa [normalizedThirdMomentBound, Fin.prod_univ_succ, mul_assoc] using
    hlc.abs_integral_normalized_coordinate_prod_le hp ![i,j,k]

theorem inverseSqrtCovariance_mul_self (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (p : Parameter n) :
    inverseSqrtCovariance μ p * inverseSqrtCovariance μ p = inverseCovariance μ p := by
  simpa only [(inverseSqrtCovariance_isSymm (μ := μ) p).eq] using
    inverseSqrtCovariance_mul_transpose hμ hfull p

theorem logDetNoiseCoefficient_eq_trace_whitened (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (z : Fin (n+n*n) → ℝ) (k : Fin n) :
    logDetNoiseCoefficient μ k z = (whitenedCovarianceNoiseMatrix μ k z).trace := by
  have hs := inverseSqrtCovariance_mul_self hμ hfull (decodeState z)
  change logDetNoiseCoefficient μ k z = _
  unfold logDetNoiseCoefficient coordinateCovarianceMatrix
  change (inverseCovariance μ (decodeState z) * covarianceNoiseMatrix μ k z).trace = _
  rw [← hs]
  exact (Matrix.trace_mul_cycle (inverseSqrtCovariance μ (decodeState z))
    (covarianceNoiseMatrix μ k z) (inverseSqrtCovariance μ (decodeState z))).symm

theorem logDetTraceCorrection_eq_whitened (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (z : Fin (n+n*n) → ℝ) :
    logDetTraceCorrection μ z = ∑ k : Fin n,
      (whitenedCovarianceNoiseMatrix μ k z * whitenedCovarianceNoiseMatrix μ k z).trace := by
  unfold logDetTraceCorrection
  apply Finset.sum_congr rfl
  intro k _
  let S := inverseSqrtCovariance μ (decodeState z)
  let C := covarianceNoiseMatrix μ k z
  have hs : S * S = (coordinateCovarianceMatrix μ z)⁻¹ :=
    inverseSqrtCovariance_mul_self hμ hfull _
  rw [← hs]
  change ((S*S)*C*(S*S)*C).trace = ((S*C*S)*(S*C*S)).trace
  calc
    _ = (S * (S*C*S*S*C)).trace := by simp only [Matrix.mul_assoc]
    _ = ((S*C*S*S*C)*S).trace := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]

theorem trace_mul_self_eq_sum_sq {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsSymm) :
    (B*B).trace = ∑ i : Fin n, ∑ j : Fin n, (B i j)^2 := by
  unfold Matrix.trace
  simp only [Matrix.diag, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hs : B j i = B i j := congrFun (congrFun hB.eq i) j
  rw [hs]
  ring

theorem logDetTraceCorrection_nonneg (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (z : Fin (n+n*n) → ℝ) :
    0 ≤ logDetTraceCorrection μ z := by
  rw [logDetTraceCorrection_eq_whitened hμ hfull]
  apply Finset.sum_nonneg
  intro k _
  rw [trace_mul_self_eq_sum_sq (whitenedCovarianceNoiseMatrix_isSymm hμ z k)]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

theorem abs_logDetNoiseCoefficient_le (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (z : Fin (n+n*n) → ℝ)
    (hlc : measureLogConcave (law μ (decodeState z).1 (decodeState z).2)) (k : Fin n) :
    |logDetNoiseCoefficient μ k z| ≤ (n : ℝ) * normalizedThirdMomentBound n := by
  rw [logDetNoiseCoefficient_eq_trace_whitened hμ hfull]
  calc
    _ ≤ ∑ i : Fin n, |whitenedCovarianceNoiseMatrix μ k z i i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, normalizedThirdMomentBound n :=
      Finset.sum_le_sum fun i _ => abs_whitenedCovarianceNoiseMatrix_le hμ hfull z hlc i i k
    _ = _ := by simp

theorem logDetTraceCorrection_le (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (z : Fin (n+n*n) → ℝ)
    (hlc : measureLogConcave (law μ (decodeState z).1 (decodeState z).2)) :
    logDetTraceCorrection μ z ≤ (n : ℝ)^3 * (normalizedThirdMomentBound n)^2 := by
  rw [logDetTraceCorrection_eq_whitened hμ hfull]
  simp_rw [trace_mul_self_eq_sum_sq (whitenedCovarianceNoiseMatrix_isSymm hμ z _)]
  calc
    _ ≤ ∑ _k : Fin n, ∑ _i : Fin n, ∑ _j : Fin n, (normalizedThirdMomentBound n)^2 := by
      apply Finset.sum_le_sum
      intro k _
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (normalizedThirdMomentBound_pos n).le).mpr
        (abs_whitenedCovarianceNoiseMatrix_le hμ hfull z hlc i j k)
    _ = _ := by simp; ring

/-- This is the scalar quadratic-variation density of logdet's martingale part. -/
def logDetNoiseSquared (μ : Measure (Space n)) (z : Fin (n+n*n) → ℝ) : ℝ :=
  ∑ k : Fin n, (logDetNoiseCoefficient μ k z)^2

theorem logDetNoiseSquared_le (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (z : Fin (n+n*n) → ℝ)
    (hlc : measureLogConcave (law μ (decodeState z).1 (decodeState z).2)) :
    logDetNoiseSquared μ z ≤ (n : ℝ)^3 * (normalizedThirdMomentBound n)^2 := by
  unfold logDetNoiseSquared
  calc
    _ ≤ ∑ _k : Fin n, ((n : ℝ)*normalizedThirdMomentBound n)^2 := by
      apply Finset.sum_le_sum
      intro k _
      have hh := abs_logDetNoiseCoefficient_le hμ hfull z hlc k
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _)
        (mul_nonneg (Nat.cast_nonneg n) (normalizedThirdMomentBound_pos n).le)).mpr hh
    _ = _ := by simp; ring

end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.logDetTraceCorrection_le
#print axioms KLS.AdaptiveLocalization.logDetNoiseSquared_le

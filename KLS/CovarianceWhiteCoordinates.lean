import KLS.AdaptiveEnergyApriori

/-! The actual inverse covariance directions are an orthonormal frame for
the covariance quadratic form. -/
open MeasureTheory Set Matrix
open scoped BigOperators Matrix.Norms.Elementwise
noncomputable section
namespace KLS.AdaptiveLocalization
variable {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
theorem sum_smul_inverseSqrtDirection (z : Fin (n+n*n) → ℝ) (c : Fin n → ℝ) :
    (∑ k, c k • inverseSqrtDirection μ z k) =
      matrixAction (inverseSqrtCovariance μ (decodeState z)) (WithLp.toLp 2 c) := by
  apply PiLp.ext
  intro i
  change (EuclideanSpace.proj i) (∑ k, c k • inverseSqrtDirection μ z k) = _
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  change (∑ k, c k * inverseSqrtCovariance μ (decodeState z) i k) =
    ∑ k, inverseSqrtCovariance μ (decodeState z) i k * c k
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem covariance_norm_inverseSqrt_combination (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (z : Fin (n+n*n) → ℝ) (c : Fin n → ℝ) :
    inner ℝ (∑ k, c k • inverseSqrtDirection μ z k)
      (matrixAction (coordinateCovarianceMatrix μ z)
        (∑ k, c k • inverseSqrtDirection μ z k)) = ∑ k, (c k)^2 := by
  rw [sum_smul_inverseSqrtDirection, inner_matrixAction_transpose,
    (inverseSqrtCovariance_isSymm (μ := μ) (decodeState z)).eq,
    ← MomentMap.matrixAction_mul_apply, ← MomentMap.matrixAction_mul_apply]
  have hw : inverseSqrtCovariance μ (decodeState z) * coordinateCovarianceMatrix μ z *
      inverseSqrtCovariance μ (decodeState z) = 1 := by
    simpa only [coordinateCovarianceMatrix,
      (inverseSqrtCovariance_isSymm (μ := μ) (decodeState z)).eq] using
      inverseSqrtCovariance_whitens hμ hfull (decodeState z)
  rw [hw, inner_eq_coordinate_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp [matrixAction_apply, Matrix.one_apply, pow_two]

end KLS.AdaptiveLocalization
end

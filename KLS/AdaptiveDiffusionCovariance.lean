import KLS.AdaptiveCoefficients

/-! The actual principal inverse square root has diffusion covariance A^{-1}. -/
open MeasureTheory ProbabilityTheory Set Matrix
open scoped Topology BigOperators MatrixOrder Matrix.Norms.Elementwise
noncomputable section
namespace KLS.AdaptiveLocalization
variable {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

theorem inverseSqrtCovariance_mul_transpose (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (p : Parameter n) :
    inverseSqrtCovariance μ p * (inverseSqrtCovariance μ p).transpose = inverseCovariance μ p := by
  rw [(inverseSqrtCovariance_isSymm p).eq]
  unfold inverseSqrtCovariance inverseSqrtMatrix inverseCovariance
  rw [← Matrix.mul_inv_rev, CFC.sqrt_mul_sqrt_self _ (covariance_posDef hμ hfull p).posSemidef.nonneg]

theorem diffusion_linear_covariance (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (p : Parameter n) (i j : Fin n) :
    (∑ k : Fin n, (diffusion μ k p).1 i * (diffusion μ k p).1 j) = inverseCovariance μ p i j := by
  have h := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A i j)
    (inverseSqrtCovariance_mul_transpose hμ hfull p)
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, diffusion] using h

end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.inverseSqrtCovariance_mul_transpose
#print axioms KLS.AdaptiveLocalization.diffusion_linear_covariance

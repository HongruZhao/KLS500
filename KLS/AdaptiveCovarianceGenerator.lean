import KLS.AdaptiveCovarianceDerivatives
import KLS.AdaptiveCumulantCancellation
import KLS.AdaptiveScoreDecomposition

/-! The genuine adaptive covariance generator is exactly minus covariance. -/
open MeasureTheory ProbabilityTheory Set Matrix
open scoped Topology BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS.AdaptiveLocalization
variable {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

theorem projection_covariance_contraction (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (p : Parameter n) (i j : Fin n) :
    (∑ k, ProbabilityTheory.covariance (fun x : Space n => x i) (projection μ p k) (law μ p.1 p.2) *
      ProbabilityTheory.covariance (fun x : Space n => x j) (projection μ p k) (law μ p.1 p.2)) =
      covariance μ p.1 p.2 i j := by
  simp_rw [covariance_projection hμ]
  have hs : (covariance μ p.1 p.2).transpose = covariance μ p.1 p.2 :=
    (covariance_posDef hμ hfull p).isHermitian.isSymm.eq
  have hd : IsUnit (covariance μ p.1 p.2).det :=
    isUnit_iff_ne_zero.mpr (covariance_posDef hμ hfull p).det_pos.ne'
  have hm : (covariance μ p.1 p.2 * inverseSqrtCovariance μ p) *
      (covariance μ p.1 p.2 * inverseSqrtCovariance μ p).transpose = covariance μ p.1 p.2 := by
    calc
      _ = covariance μ p.1 p.2 *
          (inverseSqrtCovariance μ p * (inverseSqrtCovariance μ p).transpose) *
          (covariance μ p.1 p.2).transpose := by
        rw [Matrix.transpose_mul]
        simp only [Matrix.mul_assoc]
      _ = covariance μ p.1 p.2 * inverseCovariance μ p * covariance μ p.1 p.2 := by
        rw [inverseSqrtCovariance_mul_transpose hμ hfull p, hs]
      _ = covariance μ p.1 p.2 := by
        change covariance μ p.1 p.2 * (covariance μ p.1 p.2)⁻¹ * covariance μ p.1 p.2 = _
        rw [Matrix.mul_nonsing_inv _ hd, Matrix.one_mul]
  have he := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A i j) hm
  simpa only [Matrix.mul_apply, Matrix.transpose_apply] using he

/-- The actual Frechet generator for dc=A^{-1}a dt+A^{-1/2}dB,
dQ=A^{-1}dt; no covariance differential or process is assumed. -/
def covarianceGenerator (μ : Measure (Space n)) (i j : Fin n) (p : Parameter n) : ℝ :=
  covarianceGradient μ i j p (drift μ p) +
    1 / 2 * ∑ k : Fin n, covarianceHessian μ i j p (diffusion μ k p) (diffusion μ k p)

/-- Exact deterministic adaptive generator cancellation, with actual normalized
covariance, actual derivatives, and the actual principal inverse square root. -/
theorem covarianceGenerator_eq_neg_covariance (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (p : Parameter n) (i j : Fin n) :
    covarianceGenerator μ i j p = -covariance μ p.1 p.2 i j := by
  unfold covarianceGenerator
  rw [covarianceGradient_apply_eq_cumulant hμ, exponent_drift_eq_projection_sum hμ hfull p]
  simp_rw [covarianceHessian_apply_eq_cumulant hμ, exponent_diffusion_eq_projection]
  have hc := cumulant_score_family_identity (μ := μ) hμ (continuous_exponent p.1 p.2)
    (f := fun x => x i) (g := fun x => x j) (by fun_prop) (by fun_prop)
    (h := fun k : Fin n => projection μ p k)
    (fun k : Fin n => continuous_projection (μ := μ) p k)
  calc
    _ = -(∑ k, ProbabilityTheory.covariance (fun x : Space n => x i) (projection μ p k) (law μ p.1 p.2) *
      ProbabilityTheory.covariance (fun x : Space n => x j) (projection μ p k) (law μ p.1 p.2)) := hc
    _ = -covariance μ p.1 p.2 i j := congrArg Neg.neg (projection_covariance_contraction hμ hfull p i j)

end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.covarianceGenerator_eq_neg_covariance

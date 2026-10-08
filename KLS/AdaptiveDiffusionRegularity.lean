import KLS.MatrixInverseSqrtLipschitz
import KLS.AdaptiveCoefficients

/-! Local Lipschitz regularity of the actual adaptive diffusion coefficients.
Compact support gives smooth covariance entries; full affine support supplies
positive definiteness at every finite parameter. -/
open MeasureTheory ProbabilityTheory Set Matrix
open scoped Topology Matrix.Norms.Elementwise
noncomputable section
namespace KLS.AdaptiveLocalization

variable {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

theorem locallyLipschitz_inverseSqrtCovariance (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) :
    LocallyLipschitz (inverseSqrtCovariance μ) := by
  apply locallyLipschitz_inverseSqrtMatrix_comp
  · exact ((contDiff_covariance_matrix hμ).of_le (by simp)).locallyLipschitz
  · exact covariance_posDef hμ hfull

theorem locallyLipschitz_diffusion (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (k : Fin n) :
    LocallyLipschitz (diffusion μ k) := by
  have hcolumn : ContDiff ℝ (⊤ : ℕ∞)
      (fun A : Matrix (Fin n) (Fin n) ℝ =>
        ((fun i => A i k), (0 : Matrix (Fin n) (Fin n) ℝ))) := by
    fun_prop
  exact ((hcolumn.of_le (by simp)).locallyLipschitz).comp
    (locallyLipschitz_inverseSqrtCovariance hμ hfull)

theorem locallyLipschitz_inverseSqrtCovariance_of_isotropic
    (hμ : IsCompact μ.support) (hiso : IsIsotropic μ) :
    LocallyLipschitz (inverseSqrtCovariance μ) :=
  locallyLipschitz_inverseSqrtCovariance hμ hiso.affineSpan_support_eq_top

theorem locallyLipschitz_diffusion_of_isotropic
    (hμ : IsCompact μ.support) (hiso : IsIsotropic μ) (k : Fin n) :
    LocallyLipschitz (diffusion μ k) :=
  locallyLipschitz_diffusion hμ hiso.affineSpan_support_eq_top k

end KLS.AdaptiveLocalization
end

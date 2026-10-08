import KLS.LogConcavityCutoffApproximation
import KLS.MatrixWhitening
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.LinearAlgebra.SesquilinearForm.Star

/-!
# Actual covariance matrices of cutoff measures

The matrix is the covariance bilinear form in the standard Euclidean basis.
Its entries are proved to be the coordinate covariances, and positivity comes
from the actual positive-semidefinite covariance form. For the constructed
cutoffs, the matrices converge to the identity and are eventually positive
definite, enabling actual inverse-square-root whitening.
-/

open MeasureTheory ProbabilityTheory Set Filter Matrix Metric
open scoped ENNReal Topology

noncomputable section
namespace KLS

/-- The actual covariance bilinear form in the standard Euclidean basis. -/
def covarianceMatrix {n : ℕ} (μ : Measure (Space n)) : Matrix (Fin n) (Fin n) ℝ :=
  LinearMap.toMatrix₂ (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis (covarianceBilin μ).toBilinForm

theorem covarianceMatrix_posSemidef {n : ℕ} (μ : Measure (Space n)) :
    (covarianceMatrix μ).PosSemidef := by
  exact (LinearMap.isPosSemidef_iff_posSemidef_toMatrix
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis).mp (LinearMap.BilinForm.isPosSemidef_iff.mp isPosSemidef_covarianceBilin)

theorem covarianceMatrix_apply {n : ℕ} {μ : Measure (Space n)} [IsFiniteMeasure μ]
    (hμ : MemLp (fun x : Space n => x) 2 μ) (i j : Fin n) :
    covarianceMatrix μ i j =
      ProbabilityTheory.covariance (fun x : Space n => x i) (fun x : Space n => x j) μ := by
  rw [covarianceMatrix, LinearMap.toMatrix₂_apply, ContinuousLinearMap.toBilinForm_apply,
    covarianceBilin_apply_eq_cov hμ]
  simp only [EuclideanSpace.basisFun_inner, OrthonormalBasis.coe_toBasis]

theorem IsIsotropic.memLp_id {n : ℕ} {μ : Measure (Space n)} (hμ : IsIsotropic μ) :
    MemLp (fun x : Space n => x) 2 μ :=
  MemLp.of_eval_piLp hμ.memLp_coordinate

theorem admissibleMeasure.memLp_id_ballCutoffMeasure
    {n : ℕ} {μ : Measure (Space n)} (hμ : admissibleMeasure μ) {R : ℝ}
    (hR : μ (closedBall (0 : Space n) R) ≠ 0) (k : ℕ) :
    MemLp (fun x : Space n => x) 2 (ballCutoffMeasure μ R k) :=
  (hμ.isotropic.memLp_id.restrict _).smul_measure
    (ENNReal.inv_ne_top.mpr (cutoffMass_ne_zero hR k))

theorem admissibleMeasure.tendsto_covarianceMatrix_ballCutoffMeasure
    {n : ℕ} {μ : Measure (Space n)} (hμ : admissibleMeasure μ) {R : ℝ}
    (hR : μ (closedBall (0 : Space n) R) ≠ 0) :
    Tendsto (fun k => covarianceMatrix (ballCutoffMeasure μ R k)) atTop
      (𝓝 (1 : Matrix (Fin n) (Fin n) ℝ)) := by
  let : IsProbabilityMeasure μ := hμ.isProb
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  have heq (k : ℕ) : covarianceMatrix (ballCutoffMeasure μ R k) i j =
      ProbabilityTheory.covariance (fun x : Space n => x i) (fun x : Space n => x j)
        (ballCutoffMeasure μ R k) := by
    let : IsProbabilityMeasure (ballCutoffMeasure μ R k) :=
      isProbabilityMeasure_ballCutoffMeasure hR k
    exact covarianceMatrix_apply (hμ.memLp_id_ballCutoffMeasure hR k) i j
  simpa only [heq] using hμ.tendsto_covariance_ballCutoffMeasure hR i j

/-- Positive definiteness is derived from convergence and covariance
positivity; it is not an extra hypothesis on the cutoff family. -/
theorem admissibleMeasure.eventually_posDef_covarianceMatrix_ballCutoffMeasure
    {n : ℕ} {μ : Measure (Space n)} (hμ : admissibleMeasure μ) {R : ℝ}
    (hR : μ (closedBall (0 : Space n) R) ≠ 0) :
    ∀ᶠ k in atTop, (covarianceMatrix (ballCutoffMeasure μ R k)).PosDef :=
  eventually_posDef_of_tendsto_one (hμ.tendsto_covarianceMatrix_ballCutoffMeasure hR)
    (Eventually.of_forall fun _ => covarianceMatrix_posSemidef _)

/-- The actual whitening matrices converge to the identity. -/
theorem admissibleMeasure.tendsto_inverseSqrt_covarianceMatrix_ballCutoffMeasure
    {n : ℕ} {μ : Measure (Space n)} (hμ : admissibleMeasure μ) {R : ℝ}
    (hR : μ (closedBall (0 : Space n) R) ≠ 0) :
    Tendsto (fun k => inverseSqrtMatrix (covarianceMatrix (ballCutoffMeasure μ R k)))
      atTop (𝓝 (1 : Matrix (Fin n) (Fin n) ℝ)) :=
  tendsto_inverseSqrtMatrix_one (hμ.tendsto_covarianceMatrix_ballCutoffMeasure hR)
    (Eventually.of_forall fun _ => covarianceMatrix_posSemidef _)

end KLS
end

#print axioms KLS.covarianceMatrix_posSemidef
#print axioms KLS.covarianceMatrix_apply
#print axioms KLS.admissibleMeasure.eventually_posDef_covarianceMatrix_ballCutoffMeasure
#print axioms KLS.admissibleMeasure.tendsto_inverseSqrt_covarianceMatrix_ballCutoffMeasure

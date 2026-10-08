import KLS.AffineMomentMapContraction
import KLS.SpectralQuadraticTransport

/-!
# Actual quadratic pullback and variance transport

The original law, its linear pushforward and the transported quadratic are
related by genuine measure-map identities. The final analytic inequality
keeps the representation and diffusion-range hypotheses visible.
-/

open Matrix MeasureTheory ProbabilityTheory InnerProductSpace
open scoped BigOperators ContDiff

noncomputable section
namespace KLS

variable {n : ℕ}

theorem matrixQuadratic_matrixAction (A U : Matrix (Fin n) (Fin n) ℝ)
    (x : Space n) :
    matrixQuadratic U (matrixAction A x) = matrixQuadratic (A.transpose * U * A) x := by
  rw [matrixQuadratic_eq_inner, matrixQuadratic_eq_inner]
  rw [inner_matrixAction_transpose]
  simp only [MomentMap.matrixAction_mul_apply]

/-- The variance is transported by the actual linear image measure. -/
theorem variance_matrixQuadratic_map (μ : Measure (Space n))
    (A U : Matrix (Fin n) (Fin n) ℝ) :
    ProbabilityTheory.variance (matrixQuadratic U) (μ.map (matrixAction A)) =
      ProbabilityTheory.variance (matrixQuadratic (A.transpose * U * A)) μ := by
  rw [ProbabilityTheory.variance_map (contDiff_matrixQuadratic U).continuous.measurable.aemeasurable
    (matrixAction A).continuous.measurable.aemeasurable]
  apply ProbabilityTheory.variance_congr
  exact Filter.Eventually.of_forall (matrixQuadratic_matrixAction A U)

theorem memLp_matrixQuadratic_map_iff (μ : Measure (Space n))
    (A U : Matrix (Fin n) (Fin n) ℝ) :
    MemLp (matrixQuadratic U) 2 (μ.map (matrixAction A)) ↔
      MemLp (matrixQuadratic (A.transpose * U * A)) 2 μ := by
  rw [memLp_map_measure_iff (contDiff_matrixQuadratic U).continuous.aestronglyMeasurable
    (matrixAction A).continuous.measurable.aemeasurable]
  have heq : matrixQuadratic U ∘ matrixAction A =
      matrixQuadratic (A.transpose * U * A) := funext (matrixQuadratic_matrixAction A U)
  rw [heq]

/-- Actual spectral transport supplies the original quadratic's variance
bound in terms of the correctly ordered Hessian contraction. This remains
conditional on the stated smooth full-space target and actual range density. -/
theorem quadratic_variance_le_hessian_contraction_of_transport
    {μ : Measure (Space n)} {φ V : Space n → ℝ}
    [IsFiniteMeasure (potentialMeasure φ)] [IsProbabilityMeasure (potentialMeasure V)]
    (hφ : ContDiff ℝ 2 φ) (hV : ContDiff ℝ 2 V) (hconv : ConvexOn ℝ Set.univ V)
    (M A U B : Matrix (Fin n) (Fin n) ℝ)
    (hU : U.IsSymm) (horth : U.transpose * U = 1)
    (hgram : A.transpose * A = B) (hpull : A.transpose * U * A = M)
    (hμ : MomentMap.gradientPushforward φ = μ)
    (hpush : μ.map (matrixAction A) = potentialMeasure V)
    {L : ℝ} (hL : ∀ x, ‖fderiv ℝ (gradient φ) x‖ ≤ L)
    (hq : MemLp (matrixQuadratic M) 2 μ) (hdense : DiffusionRangeDense V) :
    ProbabilityTheory.variance (matrixQuadratic M) μ ≤
      4 * ∫ x, (B * MomentMap.hessianMatrix φ x * B * MomentMap.hessianMatrix φ x).trace
        ∂potentialMeasure φ := by
  have hp : MomentMap.linearGradientPushforward φ A = potentialMeasure V := by
    rw [MomentMap.linearGradientPushforward, hμ, hpush]
  have hqU : MemLp (matrixQuadratic U) 2 (potentialMeasure V) := by
    rw [← hpush, memLp_matrixQuadratic_map_iff, hpull]
    exact hq
  have hv := quadratic_variance_le_transported_hessian_contraction
    hφ hV hconv A U hU horth hp hL hqU hdense
  rw [← hpush, variance_matrixQuadratic_map, hpull] at hv
  simpa only [hgram] using hv

end KLS
end

#print axioms KLS.variance_matrixQuadratic_map
#print axioms KLS.memLp_matrixQuadratic_map_iff
#print axioms KLS.quadratic_variance_le_hessian_contraction_of_transport

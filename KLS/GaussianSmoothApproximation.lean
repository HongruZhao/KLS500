import KLS.IsotropicGaussianGradient
import KLS.SmoothCutoffSequence
import KLS.WeightedIntegrationByParts

/-!
# Exact Gaussian smoothing reduction for quadratic variance

The approximants are the actual normalized laws `(X+rG)/sqrt(1+r²)`.
Quadratic variances converge by their second and fourth coordinate moments.
The full original class is reduced first to the proved compact cutoffs and
then to this explicit smooth family. The remaining inequality hypothesis is
displayed; no existence or regularity of a moment-map source is presumed.
-/

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped ENNReal ContDiff Topology BigOperators

noncomputable section
namespace KLS

theorem admissibleMeasure.tendsto_matrixQuadratic_isotropicGaussianSmoothing
    {n : ℕ} {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (M : Matrix (Fin n) (Fin n) ℝ) :
    Tendsto (fun k => ∫ x, matrixQuadratic M x
      ∂KLS.isotropicGaussianSmoothing μ (cutoffScale k))
      atTop (𝓝 (∫ x, matrixQuadratic M x ∂μ)) := by
  let : IsProbabilityMeasure μ := hμ.isProb
  have heq (k : ℕ) : (∫ x, matrixQuadratic M x
      ∂KLS.isotropicGaussianSmoothing μ (cutoffScale k)) =
      ∑ i, ∑ j, M i j * ∫ x : Space n, x i * x j
        ∂KLS.isotropicGaussianSmoothing μ (cutoffScale k) :=
    (hμ.isotropicGaussianSmoothing (cutoffScale_pos k).ne').logConcave.integral_matrixQuadratic_sum M
  simp_rw [heq, hμ.logConcave.integral_matrixQuadratic_sum M]
  apply tendsto_finsetSum
  intro i _
  apply tendsto_finsetSum
  intro j _
  apply Tendsto.const_mul
  simpa [Fin.prod_univ_succ, Function.comp_def] using
    (hμ.tendsto_coordinate_moment_isotropicGaussianSmoothing ![i, j]).comp cutoffScale_tendsto_zero

theorem admissibleMeasure.tendsto_matrixQuadratic_sq_isotropicGaussianSmoothing
    {n : ℕ} {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (M : Matrix (Fin n) (Fin n) ℝ) :
    Tendsto (fun k => ∫ x, matrixQuadratic M x ^ 2
      ∂KLS.isotropicGaussianSmoothing μ (cutoffScale k))
      atTop (𝓝 (∫ x, matrixQuadratic M x ^ 2 ∂μ)) := by
  let : IsProbabilityMeasure μ := hμ.isProb
  have heq (k : ℕ) : (∫ x, matrixQuadratic M x ^ 2
      ∂KLS.isotropicGaussianSmoothing μ (cutoffScale k)) =
      ∑ i, ∑ j, ∑ a, ∑ b, (M i j * M a b) *
        ∫ x : Space n, x i * x j * x a * x b
          ∂KLS.isotropicGaussianSmoothing μ (cutoffScale k) :=
    (hμ.isotropicGaussianSmoothing (cutoffScale_pos k).ne').logConcave.integral_matrixQuadratic_sq_sum M
  simp_rw [heq, hμ.logConcave.integral_matrixQuadratic_sq_sum M]
  apply tendsto_finsetSum
  intro i _
  apply tendsto_finsetSum
  intro j _
  apply tendsto_finsetSum
  intro a _
  apply tendsto_finsetSum
  intro b _
  apply Tendsto.const_mul
  simpa [Fin.prod_univ_succ, mul_assoc, Function.comp_def] using
    (hμ.tendsto_coordinate_moment_isotropicGaussianSmoothing ![i, j, a, b]).comp
      cutoffScale_tendsto_zero

theorem admissibleMeasure.tendsto_quadraticVariance_isotropicGaussianSmoothing
    {n : ℕ} {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (M : Matrix (Fin n) (Fin n) ℝ) :
    Tendsto (fun k => ProbabilityTheory.variance (matrixQuadratic M)
      (KLS.isotropicGaussianSmoothing μ (cutoffScale k)))
      atTop (𝓝 (ProbabilityTheory.variance (matrixQuadratic M) μ)) := by
  let : IsProbabilityMeasure μ := hμ.isProb
  have heq (k : ℕ) : ProbabilityTheory.variance (matrixQuadratic M)
      (KLS.isotropicGaussianSmoothing μ (cutoffScale k)) =
      (∫ x, matrixQuadratic M x ^ 2 ∂KLS.isotropicGaussianSmoothing μ (cutoffScale k)) -
        (∫ x, matrixQuadratic M x ∂KLS.isotropicGaussianSmoothing μ (cutoffScale k)) ^ 2 :=
    ProbabilityTheory.variance_eq_sub
      ((hμ.isotropicGaussianSmoothing (cutoffScale_pos k).ne').logConcave.memLp_two_matrixQuadratic M)
  have hh := (hμ.tendsto_matrixQuadratic_sq_isotropicGaussianSmoothing M).sub
    ((hμ.tendsto_matrixQuadratic_isotropicGaussianSmoothing M).pow 2)
  simpa only [heq, ProbabilityTheory.variance_eq_sub (hμ.logConcave.memLp_two_matrixQuadratic M),
    Pi.pow_apply] using hh

/-- Exact family required after the already proved compact cutoff reduction. -/
theorem admissibleMeasure.quadraticVarianceEight_of_isotropicGaussianFamily
    {n : ℕ} {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (hfamily : ∀ ν : Measure (Space n), admissibleMeasure ν → IsCompact ν.support →
      ∀ k : ℕ, QuadraticVarianceEight (KLS.isotropicGaussianSmoothing ν (cutoffScale k))) :
    QuadraticVarianceEight μ := by
  apply hμ.quadraticVarianceEight_of_compact
  intro ν hν hc M hM
  let : IsProbabilityMeasure ν := hν.isProb
  refine ⟨hν.logConcave.memLp_two_matrixQuadratic M, ?_⟩
  apply le_of_tendsto (hν.tendsto_quadraticVariance_isotropicGaussianSmoothing M)
  exact Eventually.of_forall fun k => (hfamily ν hν hc k M hM).2

/-- A sufficient smooth-target theorem, with every approximation property
proved for the actual family. A moment-map theorem would still have to supply
its own source existence, regularity, and Hessian estimates. -/
theorem admissibleMeasure.quadraticVarianceEight_of_smooth_linear_growth
    {n : ℕ} {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (hsmooth : ∀ (ν : Measure (Space n)) (V : Space n → ℝ),
      admissibleMeasure ν → ν = potentialMeasure V → ContDiff ℝ (⊤ : ℕ∞) V →
      ConvexOn ℝ univ V →
      (∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ ∀ x, ‖gradient V x‖ ≤ a + b * ‖x‖) →
      QuadraticVarianceEight ν) : QuadraticVarianceEight μ := by
  apply hμ.quadraticVarianceEight_of_isotropicGaussianFamily
  intro ν hν hc k
  let : IsProbabilityMeasure ν := hν.isProb
  have hr := (cutoffScale_pos k).ne'
  apply hsmooth (KLS.isotropicGaussianSmoothing ν (cutoffScale k))
    (isotropicGaussianPotential ν (cutoffScale k))
  · exact hν.isotropicGaussianSmoothing hr
  · exact hν.isotropicGaussianSmoothing_eq_exp_potential hc hr
  · exact isotropicGaussianPotential_contDiff hc hr
  · exact hν.isotropicGaussianPotential_convex hc hr
  · exact exists_linear_growth_isotropicGaussianPotential hc hr

end KLS
end

#print axioms KLS.admissibleMeasure.tendsto_quadraticVariance_isotropicGaussianSmoothing
#print axioms KLS.admissibleMeasure.quadraticVarianceEight_of_isotropicGaussianFamily
#print axioms KLS.admissibleMeasure.quadraticVarianceEight_of_smooth_linear_growth

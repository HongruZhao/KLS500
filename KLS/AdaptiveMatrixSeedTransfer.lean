import KLS.ThirdCumulantMatrixSeed

/-! The literal covariance-noise matrices are the coordinate third cumulants
of the actual centered, whitened law. -/
open MeasureTheory ProbabilityTheory Set Matrix
open scoped Topology BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS
variable {n : ℕ}

theorem integral_normalized_coordinate_triple (μ : Measure (Space n)) (i j k : Fin n) :
    (∫ x, normalizedCenteredVector μ x i * normalizedCenteredVector μ x j *
      normalizedCenteredVector μ x k ∂μ) =
        ∫ x : Space n, x i * x j * x k ∂whitenedMeasure μ := by
  rw [whitenedMeasure, affineMatrixMeasure, integral_map
    (f := fun x : Space n => x i * x j * x k)
    (affineMatrixMap _ _).continuous.measurable.aemeasurable
    (show AEStronglyMeasurable (fun x : Space n => x i * x j * x k) _ from
      (by fun_prop : Continuous (fun x : Space n => x i * x j * x k)).aestronglyMeasurable)]
  simp_rw [normalizedCenteredVector_eq_affine]

namespace AdaptiveLocalization
variable {μ : Measure (Space n)} [IsProbabilityMeasure μ]

theorem whitenedCovarianceNoiseMatrix_eq_thirdCumulantMatrix
    (hμ : IsCompact μ.support) (z : Fin (n+n*n) → ℝ) (k : Fin n) :
    whitenedCovarianceNoiseMatrix μ k z =
      thirdCumulantMatrix (whitenedMeasure (law μ (decodeState z).1 (decodeState z).2))
        (EuclideanSpace.single k 1) := by
  ext i j
  rw [whitenedCovarianceNoiseMatrix_eq_integral hμ,
    integral_normalized_coordinate_triple, thirdCumulantMatrix_coordinate]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

/-- At an actual parameter, a full quadratic estimate for the actual whitened
law gives the literal matrix seed for covariance noise. -/
theorem covarianceNoise_seed_eight_of_whitened_quadratic
    (hμ : IsCompact μ.support) (hfull : affineSpan ℝ μ.support = ⊤)
    (z : Fin (n+n*n) → ℝ)
    (hQ : QuadraticVarianceEight (whitenedMeasure (law μ (decodeState z).1 (decodeState z).2))) :
    ((8 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) -
      ∑ k, whitenedCovarianceNoiseMatrix μ k z * whitenedCovarianceNoiseMatrix μ k z).PosSemidef := by
  let p := decodeState z
  let := law_isProbability hμ p.1 p.2
  have hm : MemLp (fun x : Space n => x) 2 (law μ p.1 p.2) := by
    apply MemLp.of_eval_piLp
    intro j
    exact memLp_two_continuous_tilted hμ (continuous_exponent p.1 p.2) (by fun_prop)
  have hp : (covarianceMatrix (law μ p.1 p.2)).PosDef := by
    rw [← covariance_eq_covarianceMatrix hμ]
    exact covariance_posDef hμ hfull p
  have hi := whitenedMeasure_isIsotropic hm hp
  simp_rw [whitenedCovarianceNoiseMatrix_eq_thirdCumulantMatrix hμ]
  exact hi.thirdCumulantMatrix_seed_eight hQ

/-- The full admissible quadratic premise is applied to the genuinely
whitened current law, whose isotropy and log-concavity are proved. -/
theorem covarianceNoise_seed_eight_of_universal_quadratic
    (hμ : IsCompact μ.support) (hfull : affineSpan ℝ μ.support = ⊤)
    (z : Fin (n+n*n) → ℝ)
    (hlc : measureLogConcave (law μ (decodeState z).1 (decodeState z).2))
    (hQ : ∀ ν : Measure (Space n), admissibleMeasure ν → QuadraticVarianceEight ν) :
    ((8 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) -
      ∑ k, whitenedCovarianceNoiseMatrix μ k z * whitenedCovarianceNoiseMatrix μ k z).PosSemidef := by
  apply covarianceNoise_seed_eight_of_whitened_quadratic hμ hfull z
  let p := decodeState z
  let := law_isProbability hμ p.1 p.2
  have hp : (covarianceMatrix (law μ p.1 p.2)).PosDef := by
    rw [← covariance_eq_covarianceMatrix hμ]
    exact covariance_posDef hμ hfull p
  exact hQ _ ⟨inferInstance, hlc.whitenedMeasure, whitenedMeasure_isIsotropic hlc.memLp_id hp⟩

end AdaptiveLocalization
end KLS
end

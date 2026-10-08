import KLS.LocalizationLipschitz

/-! Identification with the accepted Euclidean covariance matrix. -/
open MeasureTheory ProbabilityTheory
noncomputable section
namespace KLS.StandardLocalization
variable {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

theorem memLp_id_law (hμ : IsCompact μ.support) (t : ℝ) (c : Fin n → ℝ) :
    MemLp (fun x : Space n => x) 2 (law μ t c) := by
  apply MemLp.of_eval_piLp
  intro i
  exact memLp_two_continuous_tilted hμ (continuous_exponent_state t c) (by fun_prop)

theorem covariance_eq_covarianceMatrix (hμ : IsCompact μ.support) (t : ℝ) (c : Fin n → ℝ) :
    covariance μ t c = covarianceMatrix (law μ t c) := by
  haveI := law_isProbability hμ t c
  ext i j
  exact (covarianceMatrix_apply (memLp_id_law hμ t c) i j).symm

theorem covariance_posSemidef (hμ : IsCompact μ.support) (t : ℝ) (c : Fin n → ℝ) :
    (covariance μ t c).PosSemidef := by
  rw [covariance_eq_covarianceMatrix hμ]
  exact covarianceMatrix_posSemidef _

end KLS.StandardLocalization
end
#print axioms KLS.StandardLocalization.covariance_eq_covarianceMatrix
#print axioms KLS.StandardLocalization.covariance_posSemidef

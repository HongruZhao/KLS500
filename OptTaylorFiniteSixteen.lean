import OptFiniteSixteenInduction

/-! Actual full-L2 Taylor coefficients through degree sixteen, with the
original universal measure class and all stochastic premises discharged. -/
open MeasureTheory Matrix
open scoped BigOperators
noncomputable section
namespace KLS
open AdaptiveLocalization

theorem universalDirectionalCumulantBound_finiteSixteen {d : ℕ} (hd : 1 ≤ d) (hd16 : d ≤ 16) :
    UniversalDirectionalCumulantBound d (finiteSixteenCumulantWeight d * cumulantEnergyMajorant 1 d) := by
  apply universalDirectionalCumulantBound_of_compact
  intro n μ hμ hc u
  let := hμ.isProb
  have hseed : UniformCompactMatrixSeed n := uniformCompactMatrixSeed_of_universalQuadratic
    (fun ν hν => hν.quadraticVarianceEight_unconditional)
  exact directionalCumulantSquare_le_of_compactBound hc hμ.admissibleMeasure
    (compactCumulantAndIntegratedEnergyBound_finiteSixteen hseed d hd hd16).1 u

theorem Taylor_sum_le_finiteSixteen_unconditional
    {n d : ℕ} {V : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure V)]
    (hV : ContDiff ℝ 2 V) (hμ : IsIsotropic (potentialMeasure V)) {κ : ℝ} (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian V x *ᵥ a))
    (hd : 1 ≤ d) (hd16 : d ≤ 16) (f : Lp ℝ 2 (potentialMeasure V)) :
    (∑ a : Fin d → Fin n, exponentialTiltCoordinateTaylor V f d a ^ 2) ≤
      (2 * finiteSixteenCumulantWeight d) * ‖f‖^2 := by
  have hh := Taylor_sum_le_of_universalCumulant_L2 hV hμ f hκ hlower hd
    (mul_nonneg (finiteSixteenCumulantWeight_nonneg d) (cumulantEnergyMajorant_pos (by norm_num) d).le)
    (universalDirectionalCumulantBound_finiteSixteen hd hd16)
  have hfac : (d.factorial : ℝ)^2 ≠ 0 := by positivity
  have he : 2 * (finiteSixteenCumulantWeight d * cumulantEnergyMajorant 1 d) /
      (d.factorial : ℝ)^2 = 2 * finiteSixteenCumulantWeight d := by
    simp only [cumulantEnergyMajorant, one_pow, one_mul]
    field_simp
  rwa [he] at hh

end KLS
end

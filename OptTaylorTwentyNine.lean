import OptCumulantTwentyNineInduction
import KLS.FullQuadraticVarianceBound

/-! Unconditional all-degree weighted Taylor bound for the same original
class, obtained with the preserved base amplitude and exact energy drift. -/
open MeasureTheory Set Matrix
open scoped BigOperators
noncomputable section
namespace KLS
open AdaptiveLocalization

theorem universalDirectionalCumulantBound_twentyNine {d : ℕ} (hd : 1 ≤ d) :
    UniversalDirectionalCumulantBound d ((1/20 : ℝ) * twentyNineRankWeight d * cumulantEnergyMajorant 29 d) := by
  apply universalDirectionalCumulantBound_of_compact
  intro n μ hμ hc u
  let := hμ.isProb
  have hseed : UniformCompactMatrixSeed n := uniformCompactMatrixSeed_of_universalQuadratic
    (fun ν hν => hν.quadraticVarianceEight_unconditional)
  exact directionalCumulantSquare_le_of_compactBound hc hμ.admissibleMeasure
    (compactCumulantAndIntegratedEnergyBound_twentyNine hseed d hd).1 u

theorem cumulantEnergyMajorant_Taylor_size_twentyNine (d : ℕ) :
    2 * ((1/20 : ℝ) * twentyNineRankWeight d * cumulantEnergyMajorant 29 d) / (d.factorial : ℝ)^2 ≤
      (Real.sqrt 29) ^ (2*d) := by
  have hfac : (d.factorial : ℝ)^2 ≠ 0 := by positivity
  have hs : (Real.sqrt 29)^2 = (29 : ℝ) := Real.sq_sqrt (by norm_num)
  have hq : twentyNineRankWeight d ≤ 3 := twentyNineRankWeight_le_three d
  rw [cumulantEnergyMajorant, pow_mul, hs]
  have hc : 2 * ((1/20 : ℝ) * twentyNineRankWeight d * (29^d * (d.factorial : ℝ)^2)) /
      (d.factorial : ℝ)^2 = (1/10 : ℝ) * twentyNineRankWeight d * 29^d := by field_simp; ring
  rw [hc]
  have h := mul_le_mul_of_nonneg_right hq (show (0 : ℝ) ≤ 29^d by positivity)
  nlinarith [show (0 : ℝ) ≤ 29^d by positivity]

theorem weightedCoordinateTaylorBound_sqrt29_unconditional
    {n : ℕ} {V : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure V)]
    (hV : ContDiff ℝ 2 V) (hμ : IsIsotropic (potentialMeasure V)) {κ : ℝ} (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian V x *ᵥ a)) :
    WeightedCoordinateTaylorBound V (Real.sqrt 29) := by
  exact weightedCoordinateTaylorBound_of_universalCumulant hV hμ hκ hlower
    (fun d => (1/20 : ℝ) * twentyNineRankWeight d * cumulantEnergyMajorant 29 d)
    (fun d _ => mul_nonneg (mul_nonneg (by norm_num) (twentyNineRankWeight_pos d).le)
      (cumulantEnergyMajorant_pos (by norm_num) d).le)
    (fun d _ => cumulantEnergyMajorant_Taylor_size_twentyNine d)
    (fun _ hd => universalDirectionalCumulantBound_twentyNine hd)

theorem one_le_sqrt29 : (1 : ℝ) ≤ Real.sqrt 29 := by
  exact (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)

end KLS
end

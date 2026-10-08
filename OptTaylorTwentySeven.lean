import OptTwentySevenInduction
import OptFullL2SharpTransfer

/-! Unconditional all-degree coefficients for the actual full L2 class. -/
open MeasureTheory Matrix
open scoped BigOperators
noncomputable section
namespace KLS
open AdaptiveLocalization

theorem universalDirectionalCumulantBound_twentySeven {d : ℕ} (hd : 1 ≤ d) :
    UniversalDirectionalCumulantBound d
      ((43/2000 : ℝ)*twentySevenCumulantWeight d*cumulantEnergyMajorant (27) d) := by
  apply universalDirectionalCumulantBound_of_compact
  intro n μ hμ hc u
  let := hμ.isProb
  have hseed : UniformCompactMatrixSeed n := uniformCompactMatrixSeed_of_universalQuadratic
    (fun ν hν => hν.quadraticVarianceEight_unconditional)
  exact directionalCumulantSquare_le_of_compactBound hc hμ.admissibleMeasure
    (compactCumulantAndIntegratedEnergyBound_twentySeven hseed d hd).1 u

theorem Taylor_sum_le_twentySeven_unconditional
    {n d : ℕ} {V : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure V)]
    (hV : ContDiff ℝ 2 V) (hμ : IsIsotropic (potentialMeasure V)) {κ : ℝ} (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ), κ*(a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian V x *ᵥ a))
    (hd : 1 ≤ d) (f : Lp ℝ 2 (potentialMeasure V)) :
    (∑ a : Fin d → Fin n, exponentialTiltCoordinateTaylor V f d a^2) ≤
      ((43/2000 : ℝ)*twentySevenCumulantWeight d*(27)^d)*‖f‖^2 := by
  have hh := Taylor_sum_le_of_universalCumulant_L2_sharp hV hμ f hκ hlower hd
    (mul_nonneg (mul_nonneg (by norm_num) (twentySevenCumulantWeight_pos d).le)
      (cumulantEnergyMajorant_pos (by norm_num) d).le)
    (universalDirectionalCumulantBound_twentySeven hd)
  have hfac : (d.factorial : ℝ)^2 ≠ 0 := by positivity
  have he : ((43/2000 : ℝ)*twentySevenCumulantWeight d*cumulantEnergyMajorant (27) d) /
      (d.factorial : ℝ)^2 = (43/2000 : ℝ)*twentySevenCumulantWeight d*(27)^d := by
    simp only [cumulantEnergyMajorant]
    field_simp
  rwa [he] at hh

theorem twentySevenCumulantWeight_le_two (d : ℕ) : twentySevenCumulantWeight d ≤ 2 := by
  by_cases hd : 16 ≤ d
  · rw [twentySevenCumulantWeight_large hd]
    norm_num
  · interval_cases d <;> norm_num [twentySevenCumulantWeight]

theorem weightedCoordinateTaylorBound_sqrt27_unconditional
    {n : ℕ} {V : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure V)]
    (hV : ContDiff ℝ 2 V) (hμ : IsIsotropic (potentialMeasure V)) {κ : ℝ} (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ), κ*(a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian V x *ᵥ a)) :
    WeightedCoordinateTaylorBound V (Real.sqrt (27)) := by
  intro d hd f
  have hh := Taylor_sum_le_twentySeven_unconditional hV hμ hκ hlower hd f
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have hq := twentySevenCumulantWeight_le_two d
  have hs : (Real.sqrt (27))^2 = (27 : ℝ) := Real.sq_sqrt (by norm_num)
  rw [pow_mul, hs]
  have he : (43/2000 : ℝ)*twentySevenCumulantWeight d ≤ 1 := by linarith
  simpa only [one_mul] using mul_le_mul_of_nonneg_right he (show (0 : ℝ) ≤ (27)^d by positivity)

theorem one_le_sqrt27 : (1 : ℝ) ≤ Real.sqrt (27) := by
  exact (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)

end KLS
end

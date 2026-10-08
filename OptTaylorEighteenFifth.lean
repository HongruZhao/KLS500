import OptEighteenFifthInduction
import OptFullL2SharpTransfer

set_option maxRecDepth 8192

/-! All-degree coefficients for the actual full L2 class, with the cubic seed displayed. -/
open MeasureTheory Matrix
open scoped BigOperators
noncomputable section
namespace KLS
open AdaptiveLocalization

theorem universalDirectionalCumulantBound_eighteenFifth_of_cubicSeed (hcubic : ∀ n, UniformCompactCubicSeed n) {d : ℕ} (hd : 1 ≤ d) :
    UniversalDirectionalCumulantBound d
      ((63/500 : ℝ)*eighteenFifthCumulantWeight d*cumulantEnergyMajorant (91/5) d) := by
  apply universalDirectionalCumulantBound_of_compact
  intro n μ hμ hc u
  let := hμ.isProb
  have hseed : UniformCompactMatrixSeed n := uniformCompactMatrixSeed_of_universalQuadratic
    (fun ν hν => hν.quadraticVarianceEight_unconditional)
  exact directionalCumulantSquare_le_of_compactBound hc hμ.admissibleMeasure
    (compactCumulantAndIntegratedEnergyBound_eighteenFifth hseed (hcubic n) d hd).1 u

theorem Taylor_sum_le_eighteenFifth_of_cubicSeed (hcubic : ∀ n, UniformCompactCubicSeed n)
    {n d : ℕ} {V : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure V)]
    (hV : ContDiff ℝ 2 V) (hμ : IsIsotropic (potentialMeasure V)) {κ : ℝ} (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ), κ*(a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian V x *ᵥ a))
    (hd : 1 ≤ d) (f : Lp ℝ 2 (potentialMeasure V)) :
    (∑ a : Fin d → Fin n, exponentialTiltCoordinateTaylor V f d a^2) ≤
      ((63/500 : ℝ)*eighteenFifthCumulantWeight d*(91/5)^d)*‖f‖^2 := by
  have hh := Taylor_sum_le_of_universalCumulant_L2_sharp hV hμ f hκ hlower hd
    (mul_nonneg (mul_nonneg (by norm_num) (eighteenFifthCumulantWeight_pos d).le)
      (cumulantEnergyMajorant_pos (by norm_num) d).le)
    (universalDirectionalCumulantBound_eighteenFifth_of_cubicSeed hcubic hd)
  have hfac : (d.factorial : ℝ)^2 ≠ 0 := by positivity
  have he : ((63/500 : ℝ)*eighteenFifthCumulantWeight d*cumulantEnergyMajorant (91/5) d) /
      (d.factorial : ℝ)^2 = (63/500 : ℝ)*eighteenFifthCumulantWeight d*(91/5)^d := by
    simp only [cumulantEnergyMajorant]
    field_simp
  rwa [he] at hh

theorem eighteenFifthCumulantWeight_le_two (d : ℕ) : eighteenFifthCumulantWeight d ≤ 2 := by
  exact (eighteenFifthCumulantWeight_le_one d).trans (by norm_num)

theorem weightedCoordinateTaylorBound_sqrt91over5_of_cubicSeed (hcubic : ∀ n, UniformCompactCubicSeed n)
    {n : ℕ} {V : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure V)]
    (hV : ContDiff ℝ 2 V) (hμ : IsIsotropic (potentialMeasure V)) {κ : ℝ} (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ), κ*(a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian V x *ᵥ a)) :
    WeightedCoordinateTaylorBound V (Real.sqrt (91/5)) := by
  intro d hd f
  have hh := Taylor_sum_le_eighteenFifth_of_cubicSeed (hcubic : ∀ n, UniformCompactCubicSeed n) hV hμ hκ hlower hd f
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have hq := eighteenFifthCumulantWeight_le_two d
  have hs : (Real.sqrt (91/5))^2 = (91/5 : ℝ) := Real.sq_sqrt (by norm_num)
  rw [pow_mul, hs]
  have he : (63/500 : ℝ)*eighteenFifthCumulantWeight d ≤ 1 := by linarith
  simpa only [one_mul] using mul_le_mul_of_nonneg_right he (show (0 : ℝ) ≤ (91/5)^d by positivity)

theorem one_le_sqrt91over5 : (1 : ℝ) ≤ Real.sqrt (91/5) := by
  exact (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)

end KLS
end

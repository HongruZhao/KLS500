import OptRankSymmetric128Induction
import OptFullL2SharpTransfer

set_option maxRecDepth 8192

/-! Actual full-L2 Taylor coefficients through degree sixteen, with the
original universal measure class and the cubic process seed explicitly retained. -/
open MeasureTheory Matrix
open scoped BigOperators
noncomputable section
namespace KLS
open AdaptiveLocalization

theorem universalDirectionalCumulantBound_rankSymmetric128_of_cubicSeed (hcubic : ∀ n, UniformCompactCubicSeed n) {d : ℕ} (hd : 1 ≤ d) (hd128 : d ≤ 128) :
    UniversalDirectionalCumulantBound d (rankSymmetric128CumulantWeight d * cumulantEnergyMajorant 1 d) := by
  apply universalDirectionalCumulantBound_of_compact
  intro n μ hμ hc u
  let := hμ.isProb
  have hseed : UniformCompactMatrixSeed n := uniformCompactMatrixSeed_of_universalQuadratic
    (fun ν hν => hν.quadraticVarianceEight_unconditional)
  exact directionalCumulantSquare_le_of_compactBound hc hμ.admissibleMeasure
    (compactCumulantAndIntegratedEnergyBound_rankSymmetric128 hseed (hcubic n) d hd hd128).1 u

theorem Taylor_sum_le_rankSymmetric128_of_cubicSeed (hcubic : ∀ n, UniformCompactCubicSeed n)
    {n d : ℕ} {V : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure V)]
    (hV : ContDiff ℝ 2 V) (hμ : IsIsotropic (potentialMeasure V)) {κ : ℝ} (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian V x *ᵥ a))
    (hd : 1 ≤ d) (hd128 : d ≤ 128) (f : Lp ℝ 2 (potentialMeasure V)) :
    (∑ a : Fin d → Fin n, exponentialTiltCoordinateTaylor V f d a ^ 2) ≤
      rankSymmetric128CumulantWeight d * ‖f‖^2 := by
  have hh := Taylor_sum_le_of_universalCumulant_L2_sharp hV hμ f hκ hlower hd
    (mul_nonneg (rankSymmetric128CumulantWeight_nonneg d) (cumulantEnergyMajorant_pos (by norm_num) d).le)
    (universalDirectionalCumulantBound_rankSymmetric128_of_cubicSeed hcubic hd hd128)
  have hfac : (d.factorial : ℝ)^2 ≠ 0 := by positivity
  have he : (rankSymmetric128CumulantWeight d * cumulantEnergyMajorant 1 d) /
      (d.factorial : ℝ)^2 = rankSymmetric128CumulantWeight d := by
    simp only [cumulantEnergyMajorant, one_pow, one_mul]
    field_simp
  rwa [he] at hh

end KLS
end

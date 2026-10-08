import OptTaylorRankSymmetric256
import OptActualCubicPathSeed

set_option maxRecDepth 8192

/-! The actual cubic path seed closes the finite full-L2 bound through degree256. -/
open MeasureTheory Matrix
open scoped BigOperators
noncomputable section
namespace KLS
open AdaptiveLocalization

theorem universalDirectionalCumulantBound_rankSymmetric256 {d : ℕ} (hd : 1 ≤ d) (hd256 : d ≤ 256) :
    UniversalDirectionalCumulantBound d (rankSymmetric256CumulantWeight d * cumulantEnergyMajorant 1 d) :=
  universalDirectionalCumulantBound_rankSymmetric256_of_cubicSeed uniformCompactCubicSeed_unconditional hd hd256


theorem Taylor_sum_le_rankSymmetric256_unconditional
    {n d : ℕ} {V : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure V)]
    (hV : ContDiff ℝ 2 V) (hμ : IsIsotropic (potentialMeasure V)) {κ : ℝ} (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian V x *ᵥ a))
    (hd : 1 ≤ d) (hd256 : d ≤ 256) (f : Lp ℝ 2 (potentialMeasure V)) :
    (∑ a : Fin d → Fin n, exponentialTiltCoordinateTaylor V f d a^2) ≤
      rankSymmetric256CumulantWeight d * ‖f‖^2 :=
  Taylor_sum_le_rankSymmetric256_of_cubicSeed uniformCompactCubicSeed_unconditional hV hμ hκ hlower hd hd256 f


end KLS
end

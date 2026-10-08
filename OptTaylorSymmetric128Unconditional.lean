import OptTaylorRankSymmetric128
import OptTaylorEighteenFifth
import OptActualCubicPathSeed

set_option maxRecDepth 8192

/-! The actual cubic path seed closes the finite and all-degree full-L2 bounds. -/
open MeasureTheory Matrix
open scoped BigOperators
noncomputable section
namespace KLS
open AdaptiveLocalization

theorem universalDirectionalCumulantBound_rankSymmetric128 {d : ℕ} (hd : 1 ≤ d) (hd128 : d ≤ 128) :
    UniversalDirectionalCumulantBound d (rankSymmetric128CumulantWeight d * cumulantEnergyMajorant 1 d) :=
  universalDirectionalCumulantBound_rankSymmetric128_of_cubicSeed uniformCompactCubicSeed_unconditional hd hd128

theorem universalDirectionalCumulantBound_eighteenFifth {d : ℕ} (hd : 1 ≤ d) :
    UniversalDirectionalCumulantBound d
      ((63/500 : ℝ)*eighteenFifthCumulantWeight d*cumulantEnergyMajorant (91/5) d) :=
  universalDirectionalCumulantBound_eighteenFifth_of_cubicSeed uniformCompactCubicSeed_unconditional hd

theorem Taylor_sum_le_rankSymmetric128_unconditional
    {n d : ℕ} {V : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure V)]
    (hV : ContDiff ℝ 2 V) (hμ : IsIsotropic (potentialMeasure V)) {κ : ℝ} (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian V x *ᵥ a))
    (hd : 1 ≤ d) (hd128 : d ≤ 128) (f : Lp ℝ 2 (potentialMeasure V)) :
    (∑ a : Fin d → Fin n, exponentialTiltCoordinateTaylor V f d a^2) ≤
      rankSymmetric128CumulantWeight d * ‖f‖^2 :=
  Taylor_sum_le_rankSymmetric128_of_cubicSeed uniformCompactCubicSeed_unconditional hV hμ hκ hlower hd hd128 f

theorem Taylor_sum_le_eighteenFifth_unconditional
    {n d : ℕ} {V : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure V)]
    (hV : ContDiff ℝ 2 V) (hμ : IsIsotropic (potentialMeasure V)) {κ : ℝ} (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian V x *ᵥ a))
    (hd : 1 ≤ d) (f : Lp ℝ 2 (potentialMeasure V)) :
    (∑ a : Fin d → Fin n, exponentialTiltCoordinateTaylor V f d a^2) ≤
      ((63/500 : ℝ)*eighteenFifthCumulantWeight d*(91/5)^d)*‖f‖^2 :=
  Taylor_sum_le_eighteenFifth_of_cubicSeed uniformCompactCubicSeed_unconditional hV hμ hκ hlower hd f

theorem weightedCoordinateTaylorBound_sqrt91over5_unconditional
    {n : ℕ} {V : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure V)]
    (hV : ContDiff ℝ 2 V) (hμ : IsIsotropic (potentialMeasure V)) {κ : ℝ} (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian V x *ᵥ a)) :
    WeightedCoordinateTaylorBound V (Real.sqrt (91/5)) :=
  weightedCoordinateTaylorBound_sqrt91over5_of_cubicSeed uniformCompactCubicSeed_unconditional hV hμ hκ hlower

end KLS
end

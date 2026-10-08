import SpectralReductionRankTaylorTwentyNine
import OptTaylorFiniteSixteen

/-! Retain exact first and second Taylor bounds, insert the proved finite
degree four, eight and sixteen bounds, and use the proved envelope elsewhere. -/

open MeasureTheory Matrix Set
open scoped ContDiff RealInnerProductSpace Topology BigOperators
noncomputable section
namespace KLS.ConstantReduction

def finiteRankTaylorCoefficient (d : ℕ) : ℝ :=
  if d = 4 then 30994 else if d = 8 then 14502664734 else
  if d = 16 then 3666434786700218649794 else improvedTaylorCoefficientTwentyNine d

theorem finiteRankTaylorCoefficient_nonneg (d : ℕ) : 0 ≤ finiteRankTaylorCoefficient d := by
  unfold finiteRankTaylorCoefficient
  split_ifs <;> first | positivity | exact improvedTaylorCoefficientTwentyNine_nonneg d

theorem finiteRankTaylorCoefficient_le {d : ℕ} (hd : 32 ≤ d) :
    finiteRankTaylorCoefficient d ≤ (13 / 100 : ℝ) * 29 ^ d := by
  simpa only [finiteRankTaylorCoefficient, show d ≠ 4 by omega, show d ≠ 8 by omega,
    show d ≠ 16 by omega, ↓reduceIte] using improvedTaylorCoefficientTwentyNine_le (by omega : 4 ≤ d)

theorem weightedCoordinateTaylorCoefficientBound_finiteRank
    {n : ℕ} {φ : Space n → ℝ} {κ : ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hstrong : StrongConvexOn univ κ φ) (hiso : IsIsotropic (potentialMeasure φ)) :
    WeightedCoordinateTaylorCoefficientBound φ finiteRankTaylorCoefficient := by
  have hlower := coordinateHessian_lower_of_strongConvexOn hφ hstrong
  intro d hd f
  by_cases hd4 : d = 4
  · subst d
    convert Taylor_sum_le_finiteSixteen_unconditional hφ hiso hκ hlower (by omega : 1 ≤ 4) (by omega : 4 ≤ 16) f using 1 <;>
      norm_num [finiteRankTaylorCoefficient, finiteSixteenCumulantWeight]
  by_cases hd8 : d = 8
  · subst d
    convert Taylor_sum_le_finiteSixteen_unconditional hφ hiso hκ hlower (by omega : 1 ≤ 8) (by omega : 8 ≤ 16) f using 1 <;>
      norm_num [finiteRankTaylorCoefficient, finiteSixteenCumulantWeight]
  by_cases hd16 : d = 16
  · subst d
    convert Taylor_sum_le_finiteSixteen_unconditional hφ hiso hκ hlower (by omega : 1 ≤ 16) (by omega : 16 ≤ 16) f using 1 <;>
      norm_num [finiteRankTaylorCoefficient, finiteSixteenCumulantWeight]
  simpa [finiteRankTaylorCoefficient, hd4, hd8, hd16] using
    weightedCoordinateTaylorCoefficientBound_twentyNine hφ hκ hstrong hiso d hd f

end KLS.ConstantReduction
end

#print axioms KLS.ConstantReduction.weightedCoordinateTaylorCoefficientBound_finiteRank

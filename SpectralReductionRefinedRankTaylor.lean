import SpectralReductionCauchyRankTaylor
import OptTaylorTwentySeven

/-! Exact small Taylor ranks with the proved all-degree 27 envelope. -/
open MeasureTheory Matrix Set
open scoped ContDiff RealInnerProductSpace Topology BigOperators
noncomputable section
namespace KLS.ConstantReduction

def refinedRankTaylorCoefficient (d : ℕ) : ℝ :=
  if d ≤ 16 then cauchyRankTaylorCoefficient d else
  (43/2000 : ℝ)*twentySevenCumulantWeight d*27^d

theorem refinedRankTaylorCoefficient_nonneg (d : ℕ) : 0 ≤ refinedRankTaylorCoefficient d := by
  have hh := cauchyRankTaylorCoefficient_nonneg d
  have hq := twentySevenCumulantWeight_pos d
  unfold refinedRankTaylorCoefficient
  split_ifs <;> positivity

theorem refinedRankTaylorCoefficient_large {d : ℕ} (hd : 32 ≤ d) :
    refinedRankTaylorCoefficient d = (43/2000 : ℝ)*27^d := by
  simp [refinedRankTaylorCoefficient, show ¬d≤16 by omega,
    twentySevenCumulantWeight_large (by omega : 16≤d)]

theorem weightedCoordinateTaylorCoefficientBound_refinedRank
    {n : ℕ} {φ : Space n → ℝ} {κ : ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hstrong : StrongConvexOn univ κ φ) (hiso : IsIsotropic (potentialMeasure φ)) :
    WeightedCoordinateTaylorCoefficientBound φ refinedRankTaylorCoefficient := by
  have hlower := coordinateHessian_lower_of_strongConvexOn hφ hstrong
  intro d hd f
  by_cases hsmall : d≤16
  · simpa only [refinedRankTaylorCoefficient, hsmall, ↓reduceIte] using
      weightedCoordinateTaylorCoefficientBound_cauchyRank hφ hκ hstrong hiso d hd f
  · simpa only [refinedRankTaylorCoefficient, hsmall, ↓reduceIte] using
      Taylor_sum_le_twentySeven_unconditional hφ hiso hκ hlower hd f

end KLS.ConstantReduction
end
#print axioms KLS.ConstantReduction.weightedCoordinateTaylorCoefficientBound_refinedRank

import OptTaylorRankSymmetric256Unconditional
import SpectralReductionMoving256TaylorNumbers
import SpectralReductionIndividualRankTaylor
import OptTaylorSymmetric128Unconditional

open MeasureTheory Matrix Set
open scoped ContDiff RealInnerProductSpace Topology BigOperators
noncomputable section
namespace KLS.ConstantReduction

theorem weightedCoordinateTaylorCoefficientBound_moving256Rank
    {n : ℕ} {φ : Space n → ℝ} {κ : ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hstrong : StrongConvexOn univ κ φ) (hiso : IsIsotropic (potentialMeasure φ)) :
    WeightedCoordinateTaylorCoefficientBound φ moving256RankTaylorCoefficient := by
  have hlower := coordinateHessian_lower_of_strongConvexOn hφ hstrong
  intro d hd f
  by_cases hsmall : d ≤ 256
  · simpa only [moving256RankTaylorCoefficient,hsmall,↓reduceIte] using
      Taylor_sum_le_rankSymmetric256_unconditional hφ hiso hκ hlower hd hsmall f
  · simpa only [moving256RankTaylorCoefficient,hsmall,↓reduceIte,
      eighteenFifthCumulantWeight_large (by omega : 128 ≤ d),mul_one] using
      Taylor_sum_le_eighteenFifth_unconditional hφ hiso hκ hlower hd f

end KLS.ConstantReduction
end

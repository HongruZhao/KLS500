import SpectralReductionSharpRankTaylor
import OptTaylorRankCauchy

/-! Insert the proved finite-rank Cauchy coefficients into the sharp
all-degree28.5 Taylor sequence. -/
open MeasureTheory Matrix Set
open scoped ContDiff RealInnerProductSpace Topology BigOperators
noncomputable section
namespace KLS.ConstantReduction

def cauchyRankTaylorCoefficient (d : ℕ) : ℝ :=
  if d=4 then 15095 else if d=8 then 6886667254 else
  if d=16 then 1680049546678489114313 else sharpRankTaylorCoefficient d

theorem cauchyRankTaylorCoefficient_nonneg (d : ℕ) : 0 ≤ cauchyRankTaylorCoefficient d := by
  have hh := sharpRankTaylorCoefficient_nonneg d
  unfold cauchyRankTaylorCoefficient
  split_ifs <;> positivity

theorem cauchyRankTaylorCoefficient_large {d : ℕ} (hd : 64 ≤ d) :
    cauchyRankTaylorCoefficient d = (43/1000 : ℝ)*(57/2 : ℝ)^d := by
  simpa only [cauchyRankTaylorCoefficient, show d≠4 by omega, show d≠8 by omega,
    show d≠16 by omega, ↓reduceIte] using sharpRankTaylorCoefficient_large hd

theorem weightedCoordinateTaylorCoefficientBound_cauchyRank
    {n : ℕ} {φ : Space n → ℝ} {κ : ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hstrong : StrongConvexOn univ κ φ) (hiso : IsIsotropic (potentialMeasure φ)) :
    WeightedCoordinateTaylorCoefficientBound φ cauchyRankTaylorCoefficient := by
  have hlower := coordinateHessian_lower_of_strongConvexOn hφ hstrong
  intro d hd f
  by_cases hd4 : d=4
  · subst d
    simpa [cauchyRankTaylorCoefficient, rankCauchyCumulantWeight] using
      Taylor_sum_le_rankCauchy_unconditional hφ hiso hκ hlower (by omega : 1≤4) (by omega : 4≤16) f
  by_cases hd8 : d=8
  · subst d
    simpa [cauchyRankTaylorCoefficient, rankCauchyCumulantWeight] using
      Taylor_sum_le_rankCauchy_unconditional hφ hiso hκ hlower (by omega : 1≤8) (by omega : 8≤16) f
  by_cases hd16 : d=16
  · subst d
    simpa [cauchyRankTaylorCoefficient, rankCauchyCumulantWeight] using
      Taylor_sum_le_rankCauchy_unconditional hφ hiso hκ hlower (by omega : 1≤16) (by omega : 16≤16) f
  simpa [cauchyRankTaylorCoefficient, hd4, hd8, hd16] using
    weightedCoordinateTaylorCoefficientBound_sharpRank hφ hκ hstrong hiso d hd f

end KLS.ConstantReduction
end

#print axioms KLS.ConstantReduction.weightedCoordinateTaylorCoefficientBound_cauchyRank

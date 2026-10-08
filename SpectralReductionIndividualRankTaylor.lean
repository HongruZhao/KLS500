import SpectralReductionRefinedRankTaylor
import OptTaylorRankYoung

/-! Insert the proved finite-rank Young coefficients into the sharp
all-degree27 Taylor sequence. -/
open MeasureTheory Matrix Set
open scoped ContDiff RealInnerProductSpace Topology BigOperators
noncomputable section
namespace KLS.ConstantReduction

def individualRankTaylorCoefficient (d : ℕ) : ℝ :=
  if d=4 then 744531/50 else if d=8 then 338544323193/50 else
  if d=16 then 162677761317981112887273/100 else refinedRankTaylorCoefficient d

theorem individualRankTaylorCoefficient_nonneg (d : ℕ) : 0 ≤ individualRankTaylorCoefficient d := by
  have hh := refinedRankTaylorCoefficient_nonneg d
  unfold individualRankTaylorCoefficient
  split_ifs <;> positivity

theorem individualRankTaylorCoefficient_large {d : ℕ} (hd : 32 ≤ d) :
    individualRankTaylorCoefficient d = (43/2000 : ℝ)*(27 : ℝ)^d := by
  simpa only [individualRankTaylorCoefficient, show d≠4 by omega, show d≠8 by omega,
    show d≠16 by omega, ↓reduceIte] using refinedRankTaylorCoefficient_large hd

theorem weightedCoordinateTaylorCoefficientBound_individualRank
    {n : ℕ} {φ : Space n → ℝ} {κ : ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hstrong : StrongConvexOn univ κ φ) (hiso : IsIsotropic (potentialMeasure φ)) :
    WeightedCoordinateTaylorCoefficientBound φ individualRankTaylorCoefficient := by
  have hlower := coordinateHessian_lower_of_strongConvexOn hφ hstrong
  intro d hd f
  by_cases hd4 : d=4
  · subst d
    simpa [individualRankTaylorCoefficient, rankYoungCumulantWeight] using
      Taylor_sum_le_rankYoung_unconditional hφ hiso hκ hlower (by omega : 1≤4) (by omega : 4≤16) f
  by_cases hd8 : d=8
  · subst d
    simpa [individualRankTaylorCoefficient, rankYoungCumulantWeight] using
      Taylor_sum_le_rankYoung_unconditional hφ hiso hκ hlower (by omega : 1≤8) (by omega : 8≤16) f
  by_cases hd16 : d=16
  · subst d
    simpa [individualRankTaylorCoefficient, rankYoungCumulantWeight] using
      Taylor_sum_le_rankYoung_unconditional hφ hiso hκ hlower (by omega : 1≤16) (by omega : 16≤16) f
  simpa [individualRankTaylorCoefficient, hd4, hd8, hd16] using
    weightedCoordinateTaylorCoefficientBound_refinedRank hφ hκ hstrong hiso d hd f

end KLS.ConstantReduction
end

#print axioms KLS.ConstantReduction.weightedCoordinateTaylorCoefficientBound_individualRank

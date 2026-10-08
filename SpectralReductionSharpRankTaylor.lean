import SpectralReductionFiniteRankTaylor
import OptFullL2SharpTransfer
import OptTaylorTwentyEightHalf

/-! Full-L2 Taylor bounds with the proved combined-suspension transfer.
The exact first two ranks are retained; finite ranks and the all-degree
28.5 cumulant envelope are transferred without a factor of two. -/
open MeasureTheory Matrix Set
open scoped ContDiff RealInnerProductSpace Topology BigOperators
noncomputable section
namespace KLS.ConstantReduction

def sharpRankTaylorCoefficient (d : ℕ) : ℝ :=
  if d = 1 then 1 else if d = 2 then 2 else if d = 4 then 15497 else
  if d = 8 then 7251332367 else if d = 16 then 1833217393350109324897 else
  (43/1000 : ℝ) * twentyEightHalfCumulantWeight d * (57/2 : ℝ)^d

theorem sharpRankTaylorCoefficient_nonneg (d : ℕ) : 0 ≤ sharpRankTaylorCoefficient d := by
  have hq := twentyEightHalfCumulantWeight_pos d
  unfold sharpRankTaylorCoefficient
  split_ifs <;> positivity

theorem sharpRankTaylorCoefficient_large {d : ℕ} (hd : 64 ≤ d) :
    sharpRankTaylorCoefficient d = (43/1000 : ℝ) * (57/2 : ℝ)^d := by
  simp [sharpRankTaylorCoefficient, twentyEightHalfCumulantWeight,
    twentyEightHalfIntegralWeight_large (by omega : 33 ≤ d),
    show d ≠ 1 by omega, show d ≠ 2 by omega, show d ≠ 4 by omega,
    show d ≠ 8 by omega, show d ≠ 16 by omega]

theorem Taylor_sum_le_finiteSixteen_sharp
    {n d : ℕ} {φ : Space n → ℝ} {κ : ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (hiso : IsIsotropic (potentialMeasure φ)) (hd : 1 ≤ d) (hd16 : d ≤ 16)
    (f : Lp ℝ 2 (potentialMeasure φ)) :
    (∑ a : Fin d → Fin n, exponentialTiltCoordinateTaylor φ f d a ^ 2) ≤
      finiteSixteenCumulantWeight d * ‖f‖^2 := by
  have hh := Taylor_sum_le_of_universalCumulant_L2_sharp hφ hiso f hκ hlower hd
    (mul_nonneg (finiteSixteenCumulantWeight_nonneg d) (cumulantEnergyMajorant_pos (by norm_num) d).le)
    (universalDirectionalCumulantBound_finiteSixteen hd hd16)
  have hfac : (d.factorial : ℝ)^2 ≠ 0 := by positivity
  have he : (finiteSixteenCumulantWeight d * cumulantEnergyMajorant 1 d) /
      (d.factorial : ℝ)^2 = finiteSixteenCumulantWeight d := by
    simp only [cumulantEnergyMajorant, one_pow, one_mul]
    field_simp
  rwa [he] at hh

theorem weightedCoordinateTaylorCoefficientBound_sharpRank
    {n : ℕ} {φ : Space n → ℝ} {κ : ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hstrong : StrongConvexOn univ κ φ) (hiso : IsIsotropic (potentialMeasure φ)) :
    WeightedCoordinateTaylorCoefficientBound φ sharpRankTaylorCoefficient := by
  have hlower := coordinateHessian_lower_of_strongConvexOn hφ hstrong
  intro d hd f
  by_cases hd1 : d = 1
  · subst d
    simpa [sharpRankTaylorCoefficient, improvedTaylorCoefficientTwentyNine] using
      weightedCoordinateTaylorCoefficientBound_twentyNine hφ hκ hstrong hiso 1 (by omega) f
  by_cases hd2 : d = 2
  · subst d
    simpa [sharpRankTaylorCoefficient, improvedTaylorCoefficientTwentyNine] using
      weightedCoordinateTaylorCoefficientBound_twentyNine hφ hκ hstrong hiso 2 (by omega) f
  by_cases hd4 : d = 4
  · subst d
    simpa [sharpRankTaylorCoefficient, finiteSixteenCumulantWeight] using
      Taylor_sum_le_finiteSixteen_sharp hφ hκ hlower hiso (by omega : 1 ≤ 4) (by omega : 4 ≤ 16) f
  by_cases hd8 : d = 8
  · subst d
    simpa [sharpRankTaylorCoefficient, finiteSixteenCumulantWeight] using
      Taylor_sum_le_finiteSixteen_sharp hφ hκ hlower hiso (by omega : 1 ≤ 8) (by omega : 8 ≤ 16) f
  by_cases hd16 : d = 16
  · subst d
    simpa [sharpRankTaylorCoefficient, finiteSixteenCumulantWeight] using
      Taylor_sum_le_finiteSixteen_sharp hφ hκ hlower hiso (by omega : 1 ≤ 16) (by omega : 16 ≤ 16) f
  have hh := Taylor_sum_le_of_universalCumulant_L2_sharp hφ hiso f hκ hlower hd
    (show 0 ≤ (43/1000 : ℝ) * twentyEightHalfCumulantWeight d * cumulantEnergyMajorant (57/2) d from
      mul_nonneg (mul_nonneg (by norm_num) (twentyEightHalfCumulantWeight_pos d).le)
        (cumulantEnergyMajorant_pos (by norm_num) d).le)
    (universalDirectionalCumulantBound_twentyEightHalf hd)
  have hfac : (d.factorial : ℝ)^2 ≠ 0 := by positivity
  have he : ((43/1000 : ℝ) * twentyEightHalfCumulantWeight d * cumulantEnergyMajorant (57/2) d) /
      (d.factorial : ℝ)^2 = sharpRankTaylorCoefficient d := by
    simp only [sharpRankTaylorCoefficient, hd1, hd2, hd4, hd8, hd16, ↓reduceIte, cumulantEnergyMajorant]
    field_simp
  rwa [he] at hh

end KLS.ConstantReduction
end

#print axioms KLS.ConstantReduction.weightedCoordinateTaylorCoefficientBound_sharpRank

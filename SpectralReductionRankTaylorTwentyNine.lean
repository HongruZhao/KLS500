import SpectralReductionRankTaylor
import OptTaylorTwentyNine
import KLS.IsotropicFirstTaylor
import KLS.SecondTaylorQuadraticEquivalence

/-! The actual rank-one and rank-two Taylor constants are exactly 1 and 2.
Higher ranks retain the proved twenty-nine cumulant envelope amplitude. -/

open MeasureTheory Matrix Set
open scoped ContDiff RealInnerProductSpace Topology BigOperators
noncomputable section
namespace KLS.ConstantReduction

def improvedTaylorCoefficientTwentyNine (d : ℕ) : ℝ :=
  if d = 1 then 1 else if d = 2 then 2 else (1 / 10 : ℝ) * twentyNineRankWeight d * 29 ^ d

theorem improvedTaylorCoefficientTwentyNine_nonneg (d : ℕ) :
    0 ≤ improvedTaylorCoefficientTwentyNine d := by
  have hq := twentyNineRankWeight_pos d
  unfold improvedTaylorCoefficientTwentyNine
  split_ifs <;> positivity

theorem weightedCoordinateTaylorCoefficientBound_twentyNine
    {n : ℕ} {φ : Space n → ℝ} {κ : ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hstrong : StrongConvexOn univ κ φ) (hiso : IsIsotropic (potentialMeasure φ)) :
    WeightedCoordinateTaylorCoefficientBound φ improvedTaylorCoefficientTwentyNine := by
  have hlower := coordinateHessian_lower_of_strongConvexOn hφ hstrong
  intro d hd f
  by_cases hd1 : d = 1
  · subst d
    simpa [improvedTaylorCoefficientTwentyNine] using
      sum_exponentialTiltCoordinateTaylor_one_sq_le_norm hφ hκ hlower hiso f
  by_cases hd2 : d = 2
  · subst d
    have hadm : admissibleMeasure (potentialMeasure φ) :=
      ⟨inferInstance, measureLogConcave_potentialMeasure hφ.continuous.measurable
        (convexOn_of_strongConvexOn_nonneg hκ.le hstrong), hiso⟩
    simpa [improvedTaylorCoefficientTwentyNine] using
      hadm.quadraticVarianceEight_unconditional.secondTaylor_norm_bound hφ hκ hstrong hiso f
  have hfac : (d.factorial : ℝ) ^ 2 ≠ 0 := by positivity
  have hh := Taylor_sum_le_of_universalCumulant_L2 hφ hiso f hκ hlower hd
    (show 0 ≤ (1 / 20 : ℝ) * twentyNineRankWeight d * cumulantEnergyMajorant 29 d from
      mul_nonneg (mul_nonneg (by norm_num) (twentyNineRankWeight_pos d).le)
        (cumulantEnergyMajorant_pos (by norm_num) d).le)
    (universalDirectionalCumulantBound_twentyNine hd)
  have he : 2 * ((1 / 20 : ℝ) * twentyNineRankWeight d * cumulantEnergyMajorant 29 d) /
      (d.factorial : ℝ) ^ 2 = improvedTaylorCoefficientTwentyNine d := by
    simp only [improvedTaylorCoefficientTwentyNine, hd1, hd2, ↓reduceIte, cumulantEnergyMajorant]
    field_simp
    ring
  rwa [he] at hh

theorem twentyNineRankWeight_le_thirteen_tenths {d : ℕ} (hd : 4 ≤ d) :
    twentyNineRankWeight d ≤ 13 / 10 := by
  by_cases hlarge : 26 ≤ d
  · rw [twentyNineRankWeight_large hlarge]
    norm_num
  · interval_cases d <;> norm_num [twentyNineRankWeight]

theorem improvedTaylorCoefficientTwentyNine_le {d : ℕ} (hd : 4 ≤ d) :
    improvedTaylorCoefficientTwentyNine d ≤ (13 / 100 : ℝ) * 29 ^ d := by
  have hh := mul_le_mul_of_nonneg_right (twentyNineRankWeight_le_thirteen_tenths hd)
    (show 0 ≤ (29 : ℝ) ^ d by positivity)
  simp only [improvedTaylorCoefficientTwentyNine, show d ≠ 1 by omega,
    show d ≠ 2 by omega, ↓reduceIte]
  linarith

end KLS.ConstantReduction
end

#print axioms KLS.ConstantReduction.weightedCoordinateTaylorCoefficientBound_twentyNine
#print axioms KLS.ConstantReduction.improvedTaylorCoefficientTwentyNine_le

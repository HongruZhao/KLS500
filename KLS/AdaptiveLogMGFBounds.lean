import KLS.AdaptiveLogMGFSpatial

/-! Compact support gives global fixed-spatial-vector bounds on the actual log-MGF coefficients. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS.AdaptiveLocalization
variable {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

def logMGFUniformNoiseBound (hμ : IsCompact μ.support) (w : Space n) : ℝ :=
  averageUniformNoiseBound n (Real.exp (‖w‖ * supportNormBound hμ)) /
    Real.exp (-(‖w‖ * supportNormBound hμ))

omit [IsProbabilityMeasure μ] in
theorem logMGFUniformNoiseBound_nonneg (hμ : IsCompact μ.support) (w : Space n) :
    0 ≤ logMGFUniformNoiseBound hμ w :=
  div_nonneg (averageUniformNoiseBound_nonneg n (Real.exp_pos _).le) (Real.exp_pos _).le

theorem abs_logMGFNoiseCoefficient_le (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (w : Space n) (z : Fin (n+n*n) → ℝ)
    (hlc : measureLogConcave (law μ (decodeState z).1 (decodeState z).2)) (k : Fin n) :
    |logMGFNoiseCoefficient μ w k z| ≤ logMGFUniformNoiseBound hμ w := by
  rw [logMGFNoiseCoefficient_eq_ratio hμ w, abs_div, abs_of_pos (coordinateMGF_pos hμ w z)]
  calc
    _ ≤ averageUniformNoiseBound n (Real.exp (‖w‖ * supportNormBound hμ)) /
        coordinateAverage μ (exponentialObservable w) z :=
      div_le_div_of_nonneg_right
        (abs_averageNoiseCoefficient_le hμ hfull (continuous_exponentialObservable w).measurable
          (Real.exp_pos _).le (exponentialObservable_bound hμ w) z hlc k)
        (coordinateMGF_pos hμ w z).le
    _ ≤ logMGFUniformNoiseBound hμ w :=
      div_le_div_of_nonneg_left (averageUniformNoiseBound_nonneg n (Real.exp_pos _).le)
        (Real.exp_pos _) (coordinateMGF_bounds hμ w z).1

theorem abs_logMGFDrift_le (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (w : Space n) (z : Fin (n+n*n) → ℝ)
    (hlc : measureLogConcave (law μ (decodeState z).1 (decodeState z).2)) :
    |logMGFDrift μ w z| ≤ (1/2) * (n : ℝ) * (logMGFUniformNoiseBound hμ w)^2 := by
  unfold logMGFDrift
  rw [abs_mul, show |-(1/2 : ℝ)| = 1/2 by norm_num]
  rw [abs_of_nonneg (Finset.sum_nonneg fun k _ => sq_nonneg _)]
  have hs : (∑ k : Fin n, (logMGFNoiseCoefficient μ w k z)^2) ≤
      (n : ℝ) * (logMGFUniformNoiseBound hμ w)^2 := by
    calc
      _ ≤ ∑ _k : Fin n, (logMGFUniformNoiseBound hμ w)^2 := by
        apply Finset.sum_le_sum
        intro k _
        exact sq_le_sq.mpr (by simpa only [abs_of_nonneg (logMGFUniformNoiseBound_nonneg hμ w)] using
          abs_logMGFNoiseCoefficient_le hμ hfull w z hlc k)
      _ = _ := by simp
  norm_num at *
  nlinarith

end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.abs_logMGFNoiseCoefficient_le
#print axioms KLS.AdaptiveLocalization.abs_logMGFDrift_le

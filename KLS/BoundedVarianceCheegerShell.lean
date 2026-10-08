import KLS.DistanceRampVariance

open MeasureTheory Set Filter Metric
open scoped Topology ContDiff ENNReal NNReal

noncomputable section
namespace KLS
variable {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

/-- A supplied bounded variance inequality gives the full shell quotient bound.
The additive shell error is retained for all nonclosed measurable sets. -/
theorem boundedVariance_min_div_le_enlargement_quotient
    {K : ℝ} (hK0 : 0 < K)
    (hbound : ∀ f : Space n → ℝ, LocallyLipschitz f → Integrable (gradient f) μ →
      ∀ B : ℝ, 0 ≤ B → (∀ x, |f x| ≤ B) →
        ProbabilityTheory.variance f μ ≤ K*B*(∫ x, ‖gradient f x‖ ∂μ))
    {A : Set (Space n)} (hA : MeasurableSet A) (hne : A.Nonempty)
    {ε : ℝ} (hε : 0 < ε) :
    min (μ A) (1-μ A) /
        ENNReal.ofReal (2*K+4*ε) ≤
      (μ (thickening ε A)-μ A) / ENNReal.ofReal ε := by
  have hg := distanceRamp_integral_gradient_le μ hA hne hε
  have hv := hbound (distanceRamp A ε)
    (distanceRamp_lipschitz A hε).locallyLipschitz hg.1 1 (by norm_num : (0 : ℝ) ≤ 1)
    (fun x => by rw [abs_of_nonneg (distanceRamp_nonneg A ε x)];exact distanceRamp_le_one A hε x)
  have hl := distanceRamp_variance_shell_lower μ hA hne hε
  have hp0 : 0 ≤ (μ A).toReal := ENNReal.toReal_nonneg
  have hp1 : (μ A).toReal ≤ 1 := by
    exact_mod_cast ENNReal.toReal_mono (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) (prob_le_one (μ := μ))
  have hp : min (μ A).toReal (1-(μ A).toReal) ≤ 2*((μ A).toReal*(1-(μ A).toReal)) := by
    by_cases hh : (μ A).toReal ≤ 1/2
    · rw [min_eq_left (by linarith)]
      nlinarith
    · rw [min_eq_right (by linarith)]
      nlinarith
  have hv' := mul_le_mul_of_nonneg_left hg.2
    (show 0 ≤ K*1 by positivity)
  have hb : min (μ A).toReal (1-(μ A).toReal) ≤
      (2*K)*ε⁻¹*(μ (thickening ε A \ A)).toReal+
        4*(μ (thickening ε A \ A)).toReal := by
    nlinarith
  have hK : 0 < 2*K := mul_pos (by norm_num) hK0
  have hden : 0 < 2*K+4*ε := by positivity
  have hbr : min (μ A).toReal (1-(μ A).toReal) /
      (2*K+4*ε) ≤ (μ (thickening ε A \ A)).toReal/ε := by
    apply (div_le_div_iff₀ hden hε).2
    have hh := mul_le_mul_of_nonneg_right hb hε.le
    calc
      _ ≤ ((2*K)*ε⁻¹*(μ (thickening ε A \ A)).toReal+
          4*(μ (thickening ε A \ A)).toReal)*ε := hh
      _ = _ := by field_simp
  have hden0 : ENNReal.ofReal (2*K+4*ε) ≠ 0 :=
    (ENNReal.ofReal_pos.2 hden).ne'
  have hε0 : ENNReal.ofReal ε ≠ 0 := (ENNReal.ofReal_pos.2 hε).ne'
  have hmin : min (μ A) (1-μ A) ≠ ⊤ := ne_of_lt ((min_le_left _ _).trans_lt (measure_lt_top μ A))
  have hsub : μ (thickening ε A)-μ A ≠ ⊤ := ne_of_lt (tsub_le_self.trans_lt (measure_lt_top μ _))
  apply (ENNReal.toReal_le_toReal (ENNReal.div_ne_top hmin hden0) (ENNReal.div_ne_top hsub hε0)).1
  rw [ENNReal.toReal_div,ENNReal.toReal_div,
    ENNReal.toReal_min (measure_ne_top μ A) (by finiteness),
    ENNReal.toReal_sub_of_le (prob_le_one (μ := μ)) (by norm_num),
    ENNReal.toReal_one,ENNReal.toReal_ofReal hden.le,ENNReal.toReal_ofReal hε.le]
  rw [← measure_sdiff (self_subset_thickening hε A) hA.nullMeasurableSet (measure_ne_top μ A)]
  exact hbr

end KLS
end

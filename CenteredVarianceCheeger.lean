import KLS.DistanceRampVariance
import KLS.WeakSubgradientTransport
import KLS.BoundaryComparison

open MeasureTheory Set Filter Metric
open scoped Topology ContDiff ENNReal NNReal

noncomputable section
namespace KLS
variable {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

/-- Centering the distance ramp removes a factor two from the full shell bound.
The additive shell error is retained for all nonclosed measurable sets. -/
theorem centeredVariance_min_div_le_enlargement_quotient
    {K : ℝ} (hK0 : 0 < K)
    (hbound : ∀ f : Space n → ℝ, LocallyLipschitz f → Integrable (gradient f) μ →
      ∀ B : ℝ, 0 ≤ B → (∀ x, |f x| ≤ B) →
        ProbabilityTheory.variance f μ ≤ K*B*(∫ x, ‖gradient f x‖ ∂μ))
    {A : Set (Space n)} (hA : MeasurableSet A) (hne : A.Nonempty)
    {ε : ℝ} (hε : 0 < ε) :
    min (μ A) (1-μ A) /
        ENNReal.ofReal (K+4*ε) ≤
      (μ (thickening ε A)-μ A) / ENNReal.ofReal ε := by
  have hg := distanceRamp_integral_gradient_le μ hA hne hε
  have hgrad : gradient (fun x => distanceRamp A ε x - (1/2 : ℝ)) =
      gradient (distanceRamp A ε) := gradient_sub_const _ _
  have hv := hbound (fun x => distanceRamp A ε x - (1/2 : ℝ))
    ((distanceRamp_lipschitz A hε).locallyLipschitz.sub
      (LocallyLipschitz.const (1/2 : ℝ)))
    (by simpa only [hgrad] using hg.1) (1/2) (by norm_num : (0 : ℝ) ≤ 1/2)
    (fun x => by
      apply abs_le.mpr
      constructor
      · linarith [distanceRamp_nonneg A ε x]
      · linarith [distanceRamp_le_one A hε x])
  rw [ProbabilityTheory.variance_sub_const
    (distanceRamp_lipschitz A hε).continuous.aestronglyMeasurable] at hv
  simp only [hgrad] at hv
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
    (show 0 ≤ K*(1/2 : ℝ) by positivity)
  have hb : min (μ A).toReal (1-(μ A).toReal) ≤
      K*ε⁻¹*(μ (thickening ε A \ A)).toReal+
        4*(μ (thickening ε A \ A)).toReal := by
    nlinarith
  have hK : 0 < K := hK0
  have hden : 0 < K+4*ε := by positivity
  have hbr : min (μ A).toReal (1-(μ A).toReal) /
      (K+4*ε) ≤ (μ (thickening ε A \ A)).toReal/ε := by
    apply (div_le_div_iff₀ hden hε).2
    have hh := mul_le_mul_of_nonneg_right hb hε.le
    calc
      _ ≤ (K*ε⁻¹*(μ (thickening ε A \ A)).toReal+
          4*(μ (thickening ε A \ A)).toReal)*ε := hh
      _ = _ := by field_simp
  have hden0 : ENNReal.ofReal (K+4*ε) ≠ 0 :=
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

/-- A positive bounded-variance coefficient yields the faithful open outer
Minkowski inequality for every measurable set under any probability law. -/
theorem centeredVariance_min_div_le_openBoundaryMeasure
    {K : ℝ} (hK0 : 0 < K)
    (hbound : ∀ f : Space n → ℝ, LocallyLipschitz f → Integrable (gradient f) μ →
      ∀ B : ℝ, 0 ≤ B → (∀ x, |f x| ≤ B) →
        ProbabilityTheory.variance f μ ≤ K*B*(∫ x, ‖gradient f x‖ ∂μ))
    {A : Set (Space n)} (hA : MeasurableSet A) :
    min (μ A) (1-μ A) /
        ENNReal.ofReal (K) ≤ openBoundaryMeasure (μ) A := by
  rcases A.eq_empty_or_nonempty with rfl | hne
  · simp
  have hlim : Tendsto (fun ε : ℝ => min (μ A) (1-μ A) /
      ENNReal.ofReal (K+4*ε)) (𝓝[>] (0 : ℝ))
      (𝓝 (min (μ A) (1-μ A) /
        ENNReal.ofReal (K))) := by
    have hid : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hadd : Tendsto (fun ε : ℝ => K+4*ε)
        (𝓝[>] (0 : ℝ)) (𝓝 (K)) := by
      simpa using tendsto_const_nhds.add (hid.const_mul 4)
    exact ENNReal.Tendsto.const_div
      ((ENNReal.continuous_ofReal.tendsto _).comp hadd) (Or.inl ENNReal.ofReal_ne_top)
  calc
    _ = Filter.liminf (fun ε : ℝ => min (μ A) (1-μ A) /
        ENNReal.ofReal (K+4*ε)) (𝓝[>] (0 : ℝ)) := hlim.liminf_eq.symm
    _ ≤ _ := Filter.liminf_le_liminf (by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact centeredVariance_min_div_le_enlargement_quotient hK0 hbound hA hne hε)

/-- A positive bounded-variance coefficient gives the true open Cheeger lower
bound. No median or coarea estimate is assumed. -/
theorem centeredVariance_inv_le_openCheegerConstant
    {K : ℝ} (hK0 : 0 < K)
    (hbound : ∀ f : Space n → ℝ, LocallyLipschitz f → Integrable (gradient f) μ →
      ∀ B : ℝ, 0 ≤ B → (∀ x, |f x| ≤ B) →
        ProbabilityTheory.variance f μ ≤ K*B*(∫ x, ‖gradient f x‖ ∂μ)) :
    ENNReal.ofReal ((K)⁻¹) ≤ openCheegerConstant (μ) := by
  apply le_iInf
  intro A
  have hK : 0 < K := hK0
  have hmin0 : min (μ A.1) (1-μ A.1) ≠ 0 :=
    ne_of_gt (lt_min A.2.2.1 (tsub_pos_iff_lt.mpr A.2.2.2))
  have hmintop : min (μ A.1) (1-μ A.1) ≠ ⊤ :=
    ne_of_lt ((min_le_left _ _).trans_lt (measure_lt_top (μ) A.1))
  rw [ENNReal.ofReal_inv_of_pos hK]
  apply (ENNReal.le_div_iff_mul_le (Or.inl hmin0) (Or.inl hmintop)).mpr
  simpa only [div_eq_mul_inv,mul_comm] using
    centeredVariance_min_div_le_openBoundaryMeasure hK0 hbound A.2.1

/-- An actual bounded-variance bound gives the exact original closed-neighborhood
Cheeger lower bound for any probability law. -/
theorem centeredVariance_inv_le_cheegerConstant
    {K : ℝ} (hK0 : 0 < K)
    (hbound : ∀ f : Space n → ℝ, LocallyLipschitz f → Integrable (gradient f) μ →
      ∀ B : ℝ, 0 ≤ B → (∀ x, |f x| ≤ B) →
        ProbabilityTheory.variance f μ ≤ K*B*(∫ x, ‖gradient f x‖ ∂μ)) :
    ENNReal.ofReal ((K)⁻¹) ≤ cheegerConstant (μ) :=
  le_cheegerConstant_of_le_openCheegerConstant (μ)
    (centeredVariance_inv_le_openCheegerConstant hK0 hbound)

end KLS
end

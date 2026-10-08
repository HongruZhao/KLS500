import KLS.AdaptiveGlobalCovarianceEquation

/-! The bounded measurable scalar integral equation u=c-integral(u) has the exponential solution. -/
open MeasureTheory Set Filter
open scoped Topology
set_option maxHeartbeats 800000
noncomputable section
namespace KLS.LocalDiffusion
open LevyStochCalc

/-- Continuity and the right derivative are derived from the integral equation. -/
theorem eq_exp_neg_mul_of_integral_equation {u : ℝ → ℝ} {c C : ℝ}
    (hm : Measurable u) (hC : 0 ≤ C) (hb : ∀ t, |u t| ≤ C)
    (he : ∀ t : ℝ, 0 ≤ t → u t = c - ∫ s in Icc (0 : ℝ) t, u s ∂volume)
    {T : ℝ} (hT : 0 ≤ T) : u T = Real.exp (-T)*c := by
  have hu0 : u 0 = c := by simpa using he 0 le_rfl
  have hc : ContinuousOn u (Ici (0 : ℝ)) :=
    (continuous_const.sub (continuous_setIntegral_Icc hm hC hb)).continuousOn.congr
      (fun t ht => he t ht)
  have hd (t : ℝ) (ht : 0 ≤ t) : HasDerivWithinAt u (-u t) (Ici t) t := by
    have hi : IntervalIntegrable u volume 0 t :=
      ContinuousOn.intervalIntegrable_of_Icc ht (hc.mono Icc_subset_Ici_self)
    have hdi : HasDerivWithinAt (fun v => ∫ s in (0 : ℝ)..v, u s) (u t) (Ici t) t :=
      intervalIntegral.integral_hasDerivWithinAt_right (s := Ici t) (t := Ioi t) hi
        hm.stronglyMeasurable.stronglyMeasurableAtFilter
        ((hc t ht).mono (fun v hv => ht.trans hv.le))
    have he' (v : ℝ) (hv : 0 ≤ v) : u v = c - ∫ s in (0 : ℝ)..v, u s := by
      rw [he v hv, integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hv]
    have hdc : HasDerivWithinAt (fun v => c - ∫ s in (0 : ℝ)..v, u s) (-u t) (Ici t) t := by
      simpa only [zero_sub] using hdi.const_sub c
    exact hdc.congr
      (fun v hv => he' v (ht.trans hv)) (he' t ht)
  have hg : ContinuousOn (fun t => u t * Real.exp t) (Icc (0 : ℝ) T) :=
    (hc.mono Icc_subset_Ici_self).mul Real.continuous_exp.continuousOn
  have hg' (t : ℝ) (ht : t ∈ Ico (0 : ℝ) T) :
      HasDerivWithinAt (fun t => u t * Real.exp t) 0 (Ici t) t := by
    convert (hd t ht.1).mul (Real.hasDerivAt_exp t).hasDerivWithinAt using 1; ring
  have hconst := constant_of_has_deriv_right_zero hg hg' T (right_mem_Icc.mpr hT)
  simp only [hu0, Real.exp_zero, mul_one] at hconst
  rw [Real.exp_neg]
  have hne := (Real.exp_pos T).ne'
  apply (mul_right_cancel₀ hne)
  rw [hconst]
  field_simp

end KLS.LocalDiffusion
end
#print axioms KLS.LocalDiffusion.eq_exp_neg_mul_of_integral_equation

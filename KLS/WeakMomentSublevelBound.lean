import KLS.WeakMomentSublevelTailBound

open MeasureTheory Set Filter InnerProductSpace
open scoped ContDiff Topology NNReal ENNReal Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- An integrable absolute scalar factor can be replaced by its signed
 measurable factor. The proof uses the actual two measurable sign sets. -/
theorem integrable_signed_factor_of_abs
    {μ : Measure (Space n)} {a b : Space n → ℝ} (ha : Measurable a)
    (h : Integrable (fun x => ‖a x‖ * b x) μ) :
    Integrable (fun x => a x*b x) μ := by
  let S := {x | 0 ≤ a x}
  have hS : MeasurableSet S := measurableSet_le measurable_const ha
  have ht := (h.indicator hS).sub (h.indicator hS.compl)
  apply ht.congr
  exact Eventually.of_forall fun x => by
    change S.indicator (fun y => ‖a y‖*b y) x - Sᶜ.indicator (fun y => ‖a y‖*b y) x = a x*b x
    by_cases hx : 0 ≤ a x
    · simp only [indicator_of_mem (show x ∈ S from hx),
        indicator_of_notMem (show x ∉ Sᶜ from not_not.mpr hx),sub_zero,Real.norm_of_nonneg hx]
    · simp only [indicator_of_notMem (show x ∉ S from hx),
        indicator_of_mem (show x ∈ Sᶜ from hx),zero_sub,Real.norm_eq_abs,abs_of_neg (lt_of_not_ge hx)]
      ring

/-- The original weak potential admits an actual O(scale) L1 cutoff
 diffusion estimate. The derivative, tail energy and drift integrability
 are all derived, without classical source C2/C3 assumptions. -/
theorem weak_moment_potentialSublevelCutoff_L1_bound
    {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hconv : ConvexOn ℝ univ u) (hV : ContDiff ℝ 1 V) (hVc : ConvexOn ℝ univ V)
    {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun p => V p - (κ / 2) * ‖p‖ ^ 2))
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    (x₀ : Space n) {c C : ℝ} (hc : 0 < c)
    (hderiv : ∀ t, ‖deriv sublevelCutoffProfile t‖ ≤ C) :
    Integrable (hessianMetricDiffusion u V (potentialSublevelCutoff u x₀ c)) (potentialMeasure u) ∧
      (∫ x, ‖hessianMetricDiffusion u V (potentialSublevelCutoff u x₀ c) x‖ ∂potentialMeasure u) ≤
        c*(∫ x, ‖hessianMetricDiffusion u V (potentialHeight u x₀) x‖ ∂potentialMeasure u) *
          (C+∫ s, ‖deriv (deriv sublevelCutoffProfile) s‖) := by
  have hu := moment_contDiff_one_closedTarget hLip hconv hV.continuous hK hKc hpush
  have hG := weak_moment_gradient_lipschitz_of_uniformlyConvex_target
    hLip hconv hV hVc hκ hstrong hK hKc hpush
  have hAe := weak_moment_ae_hessian_equation_of_gradient_lipschitz
    hLip hconv hV.continuous hK hKc hpush hG
  have hρ : potentialMeasure u ≪ volume := withDensity_absolutelyContinuous _ _
  have hcomp : ∀ᵐ x ∂potentialMeasure u,
      hessianMetricDiffusion u V (potentialSublevelCutoff u x₀ c) x =
        c*deriv sublevelCutoffProfile (c*potentialHeight u x₀ x) *
          hessianMetricDiffusion u V (potentialHeight u x₀) x +
        c^2*deriv (deriv sublevelCutoffProfile) (c*potentialHeight u x₀ x) *
          inverseHessianGradientForm u (potentialHeight u x₀) x :=
    hρ.ae_le (hessianMetricDiffusion_potentialSublevelCutoff_ae_C11 hu hG V x₀ c)
  have hLW := weak_moment_integrable_potentialHeight_diffusion
    hLip hconv hV hVc hκ hstrong hK hKc hpush x₀
  let E : Space n → ℝ := fun x => c^2*‖deriv (deriv sublevelCutoffProfile) (c*potentialHeight u x₀ x)‖ *
    inverseHessianGradientForm u (potentialHeight u x₀) x
  have hE : Integrable E (potentialMeasure u) :=
    (weak_moment_potentialSublevelTail_energy_identity
      hLip hconv hV hVc hκ hstrong hK hKc hpush x₀ hc).1
  have harg : Continuous (fun x => c*potentialHeight u x₀ x) :=
    continuous_const.mul (contDiff_potentialHeight hu x₀).continuous
  have hP : Integrable (fun x => c*deriv sublevelCutoffProfile (c*potentialHeight u x₀ x) *
      hessianMetricDiffusion u V (potentialHeight u x₀) x) (potentialMeasure u) := by
    apply hLW.bdd_mul (c := c*C)
      (continuous_const.mul ((sublevelCutoffProfile_contDiff.continuous_deriv (by simp)).comp harg)).aestronglyMeasurable
    exact Eventually.of_forall fun x => by
      change ‖c*deriv sublevelCutoffProfile (c*potentialHeight u x₀ x)‖ ≤ c*C
      rw [norm_mul,Real.norm_of_nonneg hc.le]
      exact mul_le_mul_of_nonneg_left (hderiv _) hc.le
  have hS : Integrable (fun x => c^2*deriv (deriv sublevelCutoffProfile) (c*potentialHeight u x₀ x) *
      inverseHessianGradientForm u (potentialHeight u x₀) x) (potentialMeasure u) := by
    have ht := integrable_signed_factor_of_abs
      (continuous_sublevelCutoffProfile_second.comp harg).measurable
      (b := fun x => c^2*inverseHessianGradientForm u (potentialHeight u x₀) x)
      (show Integrable (fun x => ‖deriv (deriv sublevelCutoffProfile) (c*potentialHeight u x₀ x)‖ *
        (c^2*inverseHessianGradientForm u (potentialHeight u x₀) x)) (potentialMeasure u) by
          simpa only [E,mul_comm,mul_left_comm,mul_assoc] using hE)
    change Integrable (fun x => deriv (deriv sublevelCutoffProfile) (c*potentialHeight u x₀ x) *
      (c^2*inverseHessianGradientForm u (potentialHeight u x₀) x)) (potentialMeasure u) at ht
    simpa only [mul_comm,mul_left_comm,mul_assoc] using ht
  have hL : Integrable (hessianMetricDiffusion u V (potentialSublevelCutoff u x₀ c)) (potentialMeasure u) :=
    (hP.add hS).congr (hcomp.mono fun _ hx => hx.symm)
  have hmajor : Integrable (fun x => c*C*‖hessianMetricDiffusion u V (potentialHeight u x₀) x‖+E x)
      (potentialMeasure u) := (hLW.norm.const_mul _).add hE
  have hpoint : ∀ᵐ x ∂potentialMeasure u,
      ‖hessianMetricDiffusion u V (potentialSublevelCutoff u x₀ c) x‖ ≤
        c*C*‖hessianMetricDiffusion u V (potentialHeight u x₀) x‖+E x := by
    filter_upwards [hcomp,hρ.ae_le hAe] with x hx hp
    rw [hx]
    have hfirst : ‖c*deriv sublevelCutoffProfile (c*potentialHeight u x₀ x) *
        hessianMetricDiffusion u V (potentialHeight u x₀) x‖ ≤
        c*C*‖hessianMetricDiffusion u V (potentialHeight u x₀) x‖ := by
      rw [norm_mul,norm_mul,Real.norm_of_nonneg hc.le]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hderiv _) hc.le) (norm_nonneg _)
    have hsecond : ‖c^2*deriv (deriv sublevelCutoffProfile) (c*potentialHeight u x₀ x) *
        inverseHessianGradientForm u (potentialHeight u x₀) x‖ = E x := by
      simp only [E,norm_mul,norm_pow,Real.norm_of_nonneg hc.le,
        Real.norm_of_nonneg (inverseHessianGradientForm_nonneg_at (potentialHeight u x₀) hp.1)]
    exact (norm_add_le _ _).trans (add_le_add hfirst hsecond.le)
  refine ⟨hL,?_⟩
  have hi := integral_mono_ae hL.norm hmajor hpoint
  rw [integral_add (hLW.norm.const_mul _) hE,integral_const_mul] at hi
  have he := weak_moment_potentialSublevelTail_energy_le
    hLip hconv hV hVc hκ hstrong hK hKc hpush x₀ hc
  dsimp only [E] at hi
  nlinarith

end KLS
end

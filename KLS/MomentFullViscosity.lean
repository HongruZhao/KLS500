import KLS.ConvexUpperTestHessian

/-! Complete convex-class C2 test inequalities for the actual moment equation.
Upper tests have their Hessian sign derived from convexity; lower tests include
all positive semidefinite Hessians. The test gradient is identified with the
actual C1 potential's gradient at contact. -/

open MeasureTheory InnerProductSpace Matrix Set Filter
open scoped Topology ENNReal NNReal ContDiff

noncomputable section
namespace KLS

variable {n : ℕ}

lemma gradient_eq_of_differentiable_touch
    {f g : Space n → ℝ} {x₀ : Space n}
    (hf : DifferentiableAt ℝ f x₀) (hg : DifferentiableAt ℝ g x₀)
    (hcontact : f x₀ = g x₀) (htouch : ∀ᶠ x in 𝓝 x₀, f x ≤ g x) :
    gradient f x₀ = gradient g x₀ := by
  have hm : IsLocalMin (fun x => g x - f x) x₀ := by
    filter_upwards [htouch] with x hx
    change g x₀ - f x₀ ≤ g x - f x
    rw [hcontact, sub_self]
    linarith
  have hz := hm.hasFDerivAt_eq_zero (hg.hasFDerivAt.sub hf.hasFDerivAt)
  apply ext_inner_right ℝ
  intro v
  have hv := congrArg (fun F : Space n →L[ℝ] ℝ => F v) hz
  simp only [_root_.sub_apply, _root_.zero_apply] at hv
  rw [inner_gradient_left, inner_gradient_left]
  linarith

theorem moment_det_ge_density_of_any_c2_upper_touch
    {u V ψ : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : Continuous V)
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    {x₀ : Space n} (hψ : ContDiffAt ℝ 2 ψ x₀)
    (hcontact : u x₀ = ψ x₀) (htouch : ∀ᶠ x in 𝓝 x₀, u x ≤ ψ x) :
    Real.exp (-u x₀ + V (gradient u x₀)) ≤ (coordinateHessian ψ x₀).det := by
  exact det_ge_density_of_convex_c2_upper_touch hLip.continuous hc
    (continuous_real_moment_density_closedTarget hLip hc hV hK hKc hpush).continuousAt
    (fun S hS => subgradient_volume_eq_lintegral_real_moment_density
      hLip hc hV.measurable hK.measurableSet hKc hpush hS) hψ hcontact htouch

/-- Positive actual density excludes singular upper-test Hessians. This is a
conclusion about touching tests, not existence of a Hessian for u. -/
theorem moment_c2_upper_test_hessian_posDef
    {u V ψ : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : Continuous V)
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    {x₀ : Space n} (hψ : ContDiffAt ℝ 2 ψ x₀)
    (hcontact : u x₀ = ψ x₀) (htouch : ∀ᶠ x in 𝓝 x₀, u x ≤ ψ x) :
    (coordinateHessian ψ x₀).PosDef := by
  have hPSD := coordinateHessian_posSemidef_of_convex_upper_touch hc hψ hcontact htouch
  apply hPSD.posDef_iff_det_ne_zero.mpr
  exact ne_of_gt ((Real.exp_pos _).trans_le
    (moment_det_ge_density_of_any_c2_upper_touch hLip hc hV hK hKc hpush hψ hcontact htouch))

theorem moment_det_le_density_of_c2_semidefinite_lower_touch
    {u V ψ : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : Continuous V)
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    {x₀ : Space n} (hψ : ContDiffAt ℝ 2 ψ x₀)
    (hH : (coordinateHessian ψ x₀).PosSemidef)
    (hcontact : u x₀ = ψ x₀) (htouch : ∀ᶠ x in 𝓝 x₀, ψ x ≤ u x) :
    (coordinateHessian ψ x₀).det ≤ Real.exp (-u x₀ + V (gradient u x₀)) := by
  exact det_le_density_of_c2_semidefinite_lower_touch hLip.continuous hc
    (continuous_real_moment_density_closedTarget hLip hc hV hK hKc hpush).continuousAt
    (Real.exp_nonneg _) (fun S hS => subgradient_volume_eq_lintegral_real_moment_density
      hLip hc hV.measurable hK.measurableSet hKc hpush hS) hψ hH hcontact htouch

/-- The nonlinear upper viscosity inequality in the standard test-gradient
form, with no Hessian sign hypothesis on the upper test. -/
theorem moment_c2_upper_viscosity_inequality
    {u V ψ : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : Continuous V)
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    {x₀ : Space n} (hψ : ContDiffAt ℝ 2 ψ x₀)
    (hcontact : u x₀ = ψ x₀) (htouch : ∀ᶠ x in 𝓝 x₀, u x ≤ ψ x) :
    Real.exp (-u x₀ + V (gradient ψ x₀)) ≤ (coordinateHessian ψ x₀).det := by
  have hg := gradient_eq_of_differentiable_touch
    ((moment_contDiff_one_closedTarget hLip hc hV hK hKc hpush).differentiable (by norm_num) x₀)
    (hψ.differentiableAt (by norm_num)) hcontact htouch
  rw [← hg]
  exact moment_det_ge_density_of_any_c2_upper_touch hLip hc hV hK hKc hpush hψ hcontact htouch

/-- The nonlinear lower viscosity inequality in test-gradient form, on the
positive semidefinite cone of the convex Monge--Ampere equation. -/
theorem moment_c2_lower_viscosity_inequality
    {u V ψ : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : Continuous V)
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    {x₀ : Space n} (hψ : ContDiffAt ℝ 2 ψ x₀)
    (hH : (coordinateHessian ψ x₀).PosSemidef)
    (hcontact : u x₀ = ψ x₀) (htouch : ∀ᶠ x in 𝓝 x₀, ψ x ≤ u x) :
    (coordinateHessian ψ x₀).det ≤ Real.exp (-u x₀ + V (gradient ψ x₀)) := by
  have hg := gradient_eq_of_differentiable_touch
    (hψ.differentiableAt (by norm_num))
    ((moment_contDiff_one_closedTarget hLip hc hV hK hKc hpush).differentiable (by norm_num) x₀)
    hcontact.symm htouch
  rw [hg]
  exact moment_det_le_density_of_c2_semidefinite_lower_touch hLip hc hV hK hKc hpush hψ hH hcontact htouch

end KLS
end

#print axioms KLS.moment_c2_upper_test_hessian_posDef
#print axioms KLS.moment_c2_upper_viscosity_inequality
#print axioms KLS.moment_c2_lower_viscosity_inequality

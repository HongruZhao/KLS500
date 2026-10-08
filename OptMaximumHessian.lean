import OptRadialPowerHessian

/-! First and second derivative bounds at a unit point where a smooth
function touches its homogeneous radial upper envelope. -/

open Filter
open scoped Topology ContDiff RealInnerProductSpace
noncomputable section
set_option maxHeartbeats 2000000
namespace KLS.ConstantReduction

theorem derivatives_le_radial_envelope_at_unit {n r : ℕ}
    {p : Space n → ℝ} (hp : ContDiff ℝ 2 p) (_hr : 2≤r)
    {x : Space n} (hx : ‖x‖=1)
    (hmax : ∀ y, p y≤p x*‖y‖^r) :
    (∀ v, fderiv ℝ p x v=(r : ℝ)*p x*inner ℝ x v) ∧
    (∀ v, fderiv ℝ (fderiv ℝ p) x v v≤
      (r : ℝ)*p x*‖v‖^2+(r : ℝ)*((r : ℝ)-2)*p x*(inner ℝ x v)^2) := by
  have hxn : x≠0 := by intro hz; simp [hz] at hx
  let g : Space n → ℝ := fun y => p x*radialPower r y-p y
  have hR := contDiffAt_radialPower r hxn
  have hg : ContDiffAt ℝ 2 g x := (contDiffAt_const.mul hR).sub hp.contDiffAt
  have hgx : g x=0 := by simp [g,radialPower_eq_norm_pow,hx]
  have hmin : IsLocalMin g x := by
    filter_upwards [] with y
    rw [hgx]
    dsimp only [g]
    rw [radialPower_eq_norm_pow]
    exact sub_nonneg.mpr (hmax y)
  have hdg : HasFDerivAt g
      ((p x) • fderiv ℝ (radialPower r) x-fderiv ℝ p x) x :=
    (hR.differentiableAt (by norm_num)).hasFDerivAt.const_mul (p x) |>.sub
      (hp.differentiable (by norm_num) x).hasFDerivAt
  have hzero := hmin.hasFDerivAt_eq_zero hdg
  constructor
  · intro v
    have hv := congrArg (fun L : Space n →L[ℝ] ℝ => L v) hzero
    simp only [sub_apply, smul_apply,smul_eq_mul,zero_apply] at hv
    rw [fderiv_radialPower_at_unit r hx] at hv
    nlinarith
  · intro v
    have heq : fderiv ℝ g =ᶠ[𝓝 x] fun y =>
        (p x) • fderiv ℝ (radialPower r) y-fderiv ℝ p y := by
      filter_upwards [eventually_ne_nhds hxn] with y hy
      exact ((contDiffAt_radialPower r hy).differentiableAt (by norm_num)).hasFDerivAt.const_mul
        (p x) |>.sub (hp.differentiable (by norm_num) y).hasFDerivAt |>.fderiv
    have hdR := (hR.fderiv_right (m:=1) (by norm_num)).differentiableAt (by norm_num)
    have hdP := ((hp.contDiffAt (x:=x)).fderiv_right (m:=1) (by norm_num)).differentiableAt (by norm_num)
    have hdd := hdR.hasFDerivAt.const_smul (p x) |>.sub hdP.hasFDerivAt
    change HasFDerivAt (fun y => (p x) • fderiv ℝ (radialPower r) y-fderiv ℝ p y) _ x at hdd
    have hs := secondFrechet_nonneg_of_isLocalMin hg hmin v
    rw [heq.fderiv_eq,hdd.fderiv] at hs
    simp only [sub_apply,smul_apply,smul_eq_mul] at hs
    rw [secondFrechet_radialPower_at_unit r hx] at hs
    nlinarith

end KLS.ConstantReduction
end

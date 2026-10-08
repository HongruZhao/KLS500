import OptLocalMinimumHessian
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

open Filter
open scoped Topology ContDiff RealInnerProductSpace
noncomputable section
set_option maxHeartbeats 2000000
namespace KLS.ConstantReduction

def radialPower {n : ℕ} (r : ℕ) (y : Space n) : ℝ :=
  (‖y‖^2)^((r : ℝ)/2)

theorem radialPower_eq_norm_pow {n : ℕ} (r : ℕ) (y : Space n) :
    radialPower r y=‖y‖^r := by
  have hh := Real.rpow_mul (norm_nonneg y) (2 : ℝ) ((r : ℝ)/2)
  rw [show (2 : ℝ)*((r : ℝ)/2)=r by ring, Real.rpow_natCast, Real.rpow_two] at hh
  exact hh.symm

theorem contDiffAt_radialPower {n : ℕ} (r : ℕ) {x : Space n} (hx : x≠0) :
    ContDiffAt ℝ 2 (radialPower r) x := by
  exact (Real.contDiffAt_rpow_const_of_ne
    (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))).comp x (contDiff_norm_sq ℝ).contDiffAt

theorem fderiv_radialPower {n : ℕ} (r : ℕ) {x : Space n} (hx : x≠0) :
    fderiv ℝ (radialPower r) x=
      (((r : ℝ)/2)*(‖x‖^2)^((r : ℝ)/2-1)) • (2 • innerSL ℝ x) := by
  exact ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.rpow_const
    (Or.inl (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)))).fderiv

theorem fderiv_radialPower_at_unit {n : ℕ} (r : ℕ) {x : Space n} (hx : ‖x‖=1)
    (v : Space n) :
    fderiv ℝ (radialPower r) x v=(r : ℝ)*inner ℝ x v := by
  have hxn : x≠0 := by intro hz; simp [hz] at hx
  rw [fderiv_radialPower r hxn]
  simp [hx]
  ring

theorem secondFrechet_radialPower_at_unit {n : ℕ} (r : ℕ) {x : Space n} (hx : ‖x‖=1)
    (v : Space n) :
    fderiv ℝ (fderiv ℝ (radialPower r)) x v v=
      (r : ℝ)*‖v‖^2+(r : ℝ)*((r : ℝ)-2)*(inner ℝ x v)^2 := by
  have hxn : x≠0 := by intro hz; simp [hz] at hx
  let a : Space n → ℝ := fun y => ((r : ℝ)/2)*(‖y‖^2)^((r : ℝ)/2-1)
  have heq : fderiv ℝ (radialPower r) =ᶠ[𝓝 x] fun y => a y • (2 • innerSL ℝ y) := by
    filter_upwards [eventually_ne_nhds hxn] with y hy
    exact fderiv_radialPower r hy
  have ha : HasFDerivAt a ((((r : ℝ)/2)*((r : ℝ)-2)) • innerSL ℝ x) x := by
    convert ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.rpow_const
      (p:=((r : ℝ)/2-1)) (Or.inl (pow_ne_zero 2 (norm_ne_zero_iff.mpr hxn)))).const_mul
        ((r : ℝ)/2) using 1
    ext w
    simp [hx]
    ring
  have hb : HasFDerivAt (fun y : Space n => 2 • innerSL ℝ y)
      (2 • (innerSL ℝ : Space n →L[ℝ] (Space n →L[ℝ] ℝ))) x :=
    (innerSL ℝ : Space n →L[ℝ] (Space n →L[ℝ] ℝ)).hasFDerivAt.const_smul 2
  have hprod := ha.smul hb
  change HasFDerivAt (fun y => a y • (2 • innerSL ℝ y)) _ x at hprod
  have hvinner : ((innerSL ℝ : Space n →L[ℝ] (Space n →L[ℝ] ℝ)) v) v=‖v‖^2 := by
    change inner ℝ v v=‖v‖^2
    exact real_inner_self_eq_norm_sq v
  rw [heq.fderiv_eq, hprod.fderiv]
  simp [a,hx]
  rw [hvinner]
  ring

end KLS.ConstantReduction
end

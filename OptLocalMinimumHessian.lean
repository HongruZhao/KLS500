import KLS.PointwiseConvexHessian
import Mathlib.Analysis.Calculus.DerivativeTest

open Filter Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 2000000
namespace KLS.ConstantReduction

theorem secondDeriv_nonneg_of_isLocalMin {f : ℝ → ℝ} {x : ℝ}
    (hm : IsLocalMin f x) (hc : ContinuousAt f x) :
    0 ≤ deriv (deriv f) x := by
  by_contra hn
  have hn' : deriv (deriv f) x<0 := lt_of_not_ge hn
  have hx := isLocalMax_of_deriv_deriv_neg hn' hm.deriv_eq_zero hc
  have heq : f =ᶠ[𝓝 x] fun _ => f x := (hm.and hx).mono fun y hy => le_antisymm hy.2 hy.1
  have hh : deriv (deriv f) x=0 := by simpa using heq.deriv.deriv_eq
  linarith

theorem secondFrechet_nonneg_of_isLocalMin {n : ℕ} {f : Space n → ℝ} {x : Space n}
    (hf : ContDiffAt ℝ 2 f x) (hm : IsLocalMin f x) (v : Space n) :
    0 ≤ fderiv ℝ (fderiv ℝ f) x v v := by
  let F : ℝ → ℝ := fun t => f (x+t • v)
  have hline : ContinuousAt (fun t : ℝ => x+t • v) 0 := by fun_prop
  have hline' : Tendsto (fun t : ℝ => x+t • v) (𝓝 0) (𝓝 x) := by
    simpa only [zero_smul,add_zero] using hline.tendsto
  have hmin : IsLocalMin F 0 := by
    have hm' : IsLocalMin f (x+(0 : ℝ) • v) := by simpa using hm
    exact hm'.comp_continuous (g:=fun t : ℝ => x+t • v) hline
  have hc : ContinuousAt F 0 := by
    change Tendsto F (𝓝 0) (𝓝 (F 0))
    simpa only [F,zero_smul,add_zero,Function.comp_def] using hf.continuousAt.tendsto.comp hline'
  have hevent : ∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ f (x+t • v) := by
    have hh := (hf.eventually (by norm_num)).mono fun y hy => hy.differentiableAt (by norm_num)
    exact hline'.eventually hh
  have heq : deriv F =ᶠ[𝓝 (0 : ℝ)] fun t => fderiv ℝ f (x+t • v) v := by
    filter_upwards [hevent] with t ht
    exact (ht.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_affine_line x v t)).deriv
  have hdd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m:=1) (by norm_num)).differentiableAt (by norm_num)
  have hd0 : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) (x+(0 : ℝ) • v) := by
    simpa only [zero_smul,add_zero] using hdd.hasFDerivAt
  have hd := (hd0.comp_hasDerivAt 0 (hasDerivAt_affine_line x v 0)).clm_apply
    (hasDerivAt_const (0 : ℝ) v)
  have hsecond : deriv (deriv F) 0 = fderiv ℝ (fderiv ℝ f) x v v := by
    rw [heq.deriv_eq]
    simpa using hd.deriv
  rw [←hsecond]
  exact secondDeriv_nonneg_of_isLocalMin hmin hc

end KLS.ConstantReduction
end

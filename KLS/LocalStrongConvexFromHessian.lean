import KLS.WeakMomentMollifiedEllipticity
import KLS.HessianConvexConverse
import Mathlib.Analysis.Convex.Strong

open Set Filter Matrix InnerProductSpace
open scoped Topology ContDiff NNReal
noncomputable section
namespace KLS
variable {n : ℕ}

/-- Nonnegative genuine second derivatives on a convex set give convexity on
that set; smoothness outside the set is used only to state ordinary derivatives. -/
theorem convexOn_of_secondFrechet_nonneg_on
    {f : Space n → ℝ} {S : Set (Space n)} (hS : Convex ℝ S)
    (hf : ContDiff ℝ 2 f)
    (hpos : ∀ x ∈ S, ∀ v, 0 ≤ fderiv ℝ (fderiv ℝ f) x v v) :
    ConvexOn ℝ S f := by
  have hd := hf.differentiable (by norm_num)
  have hdd := (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  refine ⟨hS,?_⟩
  intro x hx y hy a b ha hb hab
  let v := y-x
  let F := fun t : ℝ => f (x+t • v)
  have hd1 (t : ℝ) : HasDerivAt F (fderiv ℝ f (x+t • v) v) t :=
    (hd _).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_affine_line x v t)
  have hd2 (t : ℝ) : HasDerivAt (fun s : ℝ => fderiv ℝ f (x+s • v) v)
      (fderiv ℝ (fderiv ℝ f) (x+t • v) v v) t := by
    simpa using ((hdd _).hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_affine_line x v t)).clm_apply (hasDerivAt_const t v)
  have hFc : ConvexOn ℝ (Icc (0 : ℝ) 1) F := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
      (fun t _ => (hd1 t).continuousAt.continuousWithinAt)
      (fun t _ => (hd1 t).hasDerivWithinAt)
      (fun t _ => (hd2 t).hasDerivWithinAt)
    intro t ht
    exact hpos _ (hS.add_smul_sub_mem hx hy (interior_subset ht)) v
  have hh := hFc.2 (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
    (show (1 : ℝ) ∈ Icc 0 1 by norm_num) ha hb hab
  have he : x+b • (y-x) = a • x+b • y := by
    have hae : a = 1-b := by linarith
    rw [hae]
    module
  simpa only [F,v,smul_eq_mul,mul_zero,mul_one,zero_add,zero_smul,add_zero,
    one_smul,add_sub_cancel,he] using hh

lemma inner_coordinateHessian_eq_secondFrechet {f : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) (x v : Space n) :
    inner ℝ v (matrixAction (coordinateHessian f x) v) =
      fderiv ℝ (fderiv ℝ f) x v v := by
  rw [← coordinateHessian_quadratic_eq hf]
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,matrixAction_apply,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- A genuine Hessian lower bound gives strong convexity on the actual convex
set, without any extension of the lower bound beyond that set. -/
theorem strongConvexOn_of_hessian_lower_on
    {f : Space n → ℝ} {S : Set (Space n)} (hS : Convex ℝ S)
    (hf : ContDiff ℝ 2 f) {μ : ℝ}
    (hlower : ∀ x ∈ S, ∀ v : Space n,
      μ * ‖v‖^2 ≤ inner ℝ v (matrixAction (coordinateHessian f x) v)) :
    StrongConvexOn S μ f := by
  let q := centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) (0 : Space n) 0 0
  let F := fun y => f y + (-μ) * q y + 0
  have hq : ContDiff ℝ 2 q := (contDiff_centeredQuadratic _ _ _ _).of_le (by simp)
  have hF : ContDiff ℝ 2 F := (hf.add (contDiff_const.mul hq)).add contDiff_const
  have hc : ConvexOn ℝ S F := by
    apply convexOn_of_secondFrechet_nonneg_on hS hF
    intro x hx v
    rw [← inner_coordinateHessian_eq_secondFrechet hF]
    have hH : coordinateHessian F x = coordinateHessian f x + (-μ) • (1 : Matrix (Fin n) (Fin n) ℝ) :=
      coordinateHessian_add_scalar_quadratic_const hf 0 (-μ) 0 x
    rw [hH,matrixAction_add_matrices,matrixAction_smul_scalar,inner_add_right,inner_smul_right,matrixAction_one_apply]
    rw [real_inner_self_eq_norm_sq]
    have hh := hlower x hx v
    linarith
  apply strongConvexOn_iff_convex.mpr
  convert hc using 1
  funext y
  simp only [F,q,centeredQuadratic_one_eq_half_norm_sq,sub_zero]
  ring

end KLS
end

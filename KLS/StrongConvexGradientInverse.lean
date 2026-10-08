import KLS.WeakMomentLocalStrongConvexity

open Set Filter InnerProductSpace
open scoped Topology ContDiff NNReal
noncomputable section
namespace KLS
variable {n : ℕ}

lemma convex_supporting_fderiv_on
    {u : Space n → ℝ} {S : Set (Space n)} (hc : ConvexOn ℝ S u)
    (hd : Differentiable ℝ u) {x y : Space n} (hx : x ∈ S) (hy : y ∈ S) :
    u x + fderiv ℝ u x (y-x) ≤ u y := by
  have hline : ConvexOn ℝ (Icc (0 : ℝ) 1) (fun t => u (x+t • (y-x))) := by
    refine ⟨convex_Icc _ _,?_⟩
    intro s hs t ht a b ha hb hab
    have he : a • (x+s • (y-x)) + b • (x+t • (y-x)) = x+(a*s+b*t) • (y-x) := by
      calc
        _ = (a+b) • x+(a*s+b*t) • (y-x) := by module
        _ = _ := by rw [hab,one_smul]
    have hh := hc.2 (hc.1.add_smul_sub_mem hx hy hs)
      (hc.1.add_smul_sub_mem hx hy ht) ha hb hab
    simpa only [he,smul_eq_mul] using hh
  have hder : HasDerivAt (fun t : ℝ => u (x+t • (y-x)))
      (fderiv ℝ u x (y-x)) 0 := by
    simpa only [Function.comp_def,zero_smul,add_zero] using
      (hd (x+(0 : ℝ) • (y-x))).hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_affine_line x (y-x) 0)
  have hh := hline.le_slope_of_hasDerivAt
    (show (0 : ℝ) ∈ Icc 0 1 by norm_num) (show (1 : ℝ) ∈ Icc 0 1 by norm_num)
    (by norm_num) hder
  simp only [slope_def_field,zero_smul,add_zero,one_smul,add_sub_cancel,sub_zero,div_one] at hh
  linarith

/-- The supporting-plane remainder of a differentiable strongly convex
function is bounded below by the actual squared displacement. -/
theorem strongConvex_supporting_gradient_on
    {u : Space n → ℝ} {S : Set (Space n)} {μ : ℝ} (hc : StrongConvexOn S μ u)
    (hd : Differentiable ℝ u) {x y : Space n} (hx : x ∈ S) (hy : y ∈ S) :
    u x + inner ℝ (gradient u x) (y-x) + (μ/2)*‖y-x‖^2 ≤ u y := by
  let F := fun z => u z - (μ/2)*‖z‖^2
  have hFc : ConvexOn ℝ S F := strongConvexOn_iff_convex.mp hc
  have hFd : Differentiable ℝ F := hd.sub
    ((differentiable_const (μ/2)).mul ((contDiff_norm_sq ℝ (n := 2)).differentiable (by norm_num)))
  have hder (w : Space n) : fderiv ℝ F x w = fderiv ℝ u x w - μ * inner ℝ x w := by
    have hh := ((hd x).hasFDerivAt.sub ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (μ/2))).fderiv
    rw [show fderiv ℝ F x = fderiv ℝ u x - (μ/2) • (2 • innerSL ℝ x) from hh]
    simp only [_root_.sub_apply,_root_.smul_apply,smul_eq_mul,innerSL_apply_apply]
    ring
  have hh := convex_supporting_fderiv_on hFc hFd hx hy
  rw [hder,← inner_gradient_left] at hh
  rw [inner_sub_right x,real_inner_self_eq_norm_sq] at hh
  dsimp only [F] at hh
  rw [norm_sub_sq_real,real_inner_comm x y]
  nlinarith

/-- Local strong convexity gives quantitative inverse control for the actual
gradient on the same convex set. No existence of a classical Hessian is used. -/
theorem gradient_inverse_norm_bound_of_strongConvexOn
    {u : Space n → ℝ} {S : Set (Space n)} {μ : ℝ}
    (hc : StrongConvexOn S μ u) (hd : Differentiable ℝ u)
    {x y : Space n} (hx : x ∈ S) (hy : y ∈ S) :
    μ * ‖y-x‖ ≤ ‖gradient u y-gradient u x‖ := by
  have hxy := strongConvex_supporting_gradient_on hc hd hx hy
  have hyx := strongConvex_supporting_gradient_on hc hd hy hx
  have he : x-y = -(y-x) := by abel
  rw [he,inner_neg_right,norm_neg] at hyx
  have hlower : μ * ‖y-x‖^2 ≤ inner ℝ (gradient u y-gradient u x) (y-x) := by
    rw [inner_sub_left]
    nlinarith
  have hupp := real_inner_le_norm (gradient u y-gradient u x) (y-x)
  by_cases heq : y=x
  · simp [heq]
  · have hnorm : 0 < ‖y-x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr heq)
    apply (mul_le_mul_iff_left₀ hnorm).mp
    nlinarith

end KLS
end

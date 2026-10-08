import KLS.PointwiseGradientHessian

open Matrix Set Filter InnerProductSpace
open scoped Topology ContDiff Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- Convexity makes the actual pointwise second derivative nonnegative when
 the actual gradient is differentiable at that point. No C2 assumption is used. -/
theorem secondFrechet_nonneg_of_gradient_differentiableAt
    {u : Space n → ℝ} (hu : Differentiable ℝ u) (hc : ConvexOn ℝ univ u)
    {x : Space n} (hg : DifferentiableAt ℝ (gradient u) x) (v : Space n) :
    0 ≤ fderiv ℝ (fderiv ℝ u) x v v := by
  have hdd := differentiableAt_fderiv_of_gradient hg
  let F : ℝ → ℝ := fun t => u (x+t • v)
  have hd (t : ℝ) : HasDerivAt F (fderiv ℝ u (x+t • v) v) t :=
    (hu _).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_affine_line x v t)
  have hmono : Monotone (deriv F) := monotoneOn_univ.mp
    ((convexOn_affine_line hc x v).monotoneOn_deriv (fun t _ => (hd t).differentiableAt))
  have heq : deriv F = fun t => fderiv ℝ u (x+t • v) v := by
    funext t
    exact (hd t).deriv
  have hd0 : HasFDerivAt (fderiv ℝ u) (fderiv ℝ (fderiv ℝ u) x) (x+(0 : ℝ) • v) := by
    simpa only [zero_smul,add_zero] using hdd.hasFDerivAt
  have hline := hd0.comp_hasDerivAt 0 (hasDerivAt_affine_line x v 0)
  have heval := hline.clm_apply (hasDerivAt_const (0 : ℝ) v)
  have hv : deriv (deriv F) 0 = fderiv ℝ (fderiv ℝ u) x v v := by
    rw [heq]
    simpa using heval.deriv
  rw [← hv]
  exact hmono.deriv_nonneg

lemma coordinateHessian_quadratic_eq_of_gradient_differentiableAt
    {u : Space n → ℝ} {x : Space n} (hg : DifferentiableAt ℝ (gradient u) x)
    (v w : Space n) :
    (∑ i : Fin n, ∑ j : Fin n, coordinateHessian u x i j * v i * w j) =
      fderiv ℝ (fderiv ℝ u) x v w := by
  have hdd := differentiableAt_fderiv_of_gradient hg
  simp_rw [coordinateHessian_eq_fderiv_fderiv hdd]
  conv_rhs => rw [euclidean_eq_sum_single v,map_sum,_root_.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul,_root_.smul_apply]
  change _ = v i * (fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1)) w
  conv_rhs => arg 2; rw [euclidean_eq_sum_single w,map_sum]
  simp only [map_smul,smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The actual coordinate Hessian of a differentiable convex function is
 positive semidefinite at every point where its gradient is differentiable. -/
theorem coordinateHessian_posSemidef_of_gradient_differentiableAt
    {u : Space n → ℝ} (hu : Differentiable ℝ u) (hc : ConvexOn ℝ univ u)
    {x : Space n} (hg : DifferentiableAt ℝ (gradient u) x) :
    (coordinateHessian u x).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact Matrix.isHermitian_iff_isSymm.mpr
      (coordinateHessian_isSymm_of_gradient_differentiableAt hu hg)
  · intro w
    have heq : star w ⬝ᵥ (coordinateHessian u x *ᵥ w) =
        ∑ i : Fin n, ∑ j : Fin n, coordinateHessian u x i j * w i * w j := by
      simp only [star_trivial,dotProduct,Matrix.mulVec,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [heq]
    change 0 ≤ ∑ i : Fin n, ∑ j : Fin n,
      coordinateHessian u x i j * (WithLp.toLp 2 w : Space n) i * (WithLp.toLp 2 w : Space n) j
    rw [coordinateHessian_quadratic_eq_of_gradient_differentiableAt hg]
    exact secondFrechet_nonneg_of_gradient_differentiableAt hu hc hg _

end KLS
end

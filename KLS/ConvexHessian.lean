import KLS.WeightedCompactSupport

/-!
# Positivity of the actual Hessian of a smooth convex potential

Convexity is restricted to each affine line. Monotonicity of the line's first
derivative gives nonnegativity of its second derivative, which is identified
with the genuine second Fréchet derivative and then with coordinate Hessian
quadratic forms.
-/

open MeasureTheory InnerProductSpace Set
open scoped BigOperators ContDiff Matrix

noncomputable section
namespace KLS

variable {n : ℕ}

lemma convexOn_affine_line {φ : Space n → ℝ} (hφ : ConvexOn ℝ univ φ)
    (x v : Space n) : ConvexOn ℝ univ (fun t : ℝ => φ (x + t • v)) := by
  refine ⟨convex_univ, ?_⟩
  intro s _ t _ a b ha hb hab
  have heq : a • (x + s • v) + b • (x + t • v) = x + (a * s + b * t) • v := by
    calc
      _ = (a + b) • x + (a * s + b * t) • v := by module
      _ = _ := by rw [hab, one_smul]
  have h := hφ.2 (mem_univ (x + s • v)) (mem_univ (x + t • v)) ha hb hab
  simpa only [heq, smul_eq_mul] using h

lemma hasDerivAt_affine_line (x v : Space n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => x + s • v) v t := by
  simpa using ((hasDerivAt_id t).smul_const v).const_add x

/-- Convexity supplies nonnegativity of the actual second directional derivative. -/
theorem secondFrechet_nonneg_of_convex {φ : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hconv : ConvexOn ℝ univ φ) (x v : Space n) :
    0 ≤ fderiv ℝ (fderiv ℝ φ) x v v := by
  have hdφ : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hddφ : Differentiable ℝ (fderiv ℝ φ) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  let F : ℝ → ℝ := fun t => φ (x + t • v)
  have hd (t : ℝ) : HasDerivAt F (fderiv ℝ φ (x + t • v) v) t :=
    (hdφ (x + t • v)).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_affine_line x v t)
  have hmono : Monotone (deriv F) := by
    exact monotoneOn_univ.mp ((convexOn_affine_line hconv x v).monotoneOn_deriv
      (fun t _ => (hd t).differentiableAt))
  have hder : deriv F = fun t => fderiv ℝ φ (x + t • v) v := by
    funext t
    exact (hd t).deriv
  have hdmap := (hddφ (x + (0 : ℝ) • v)).hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_affine_line x v 0)
  have hdmap' : HasDerivAt (fun t : ℝ => fderiv ℝ φ (x + t • v))
      (fderiv ℝ (fderiv ℝ φ) x v) 0 := by
    convert! hdmap using 1; simp
  have hdeval := hdmap'.clm_apply (hasDerivAt_const (0 : ℝ) v)
  have hd2 : deriv (deriv F) 0 = fderiv ℝ (fderiv ℝ φ) x v v := by
    rw [hder]
    simpa using hdeval.deriv
  rw [← hd2]
  exact hmono.deriv_nonneg

lemma euclidean_eq_sum_single (v : Space n) :
    v = ∑ i : Fin n, v i • EuclideanSpace.single i 1 := by
  classical
  ext j
  simp [Pi.single_apply]

/-- The coordinate Hessian quadratic form is the actual bilinear second derivative. -/
lemma coordinateHessian_quadratic_eq {φ : Space n → ℝ} (hφ : ContDiff ℝ 2 φ)
    (x u v : Space n) :
    (∑ i : Fin n, ∑ j : Fin n, coordinateHessian φ x i j * u i * v j) =
      fderiv ℝ (fderiv ℝ φ) x u v := by
  have hddφ : DifferentiableAt ℝ (fderiv ℝ φ) x :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
  simp_rw [coordinateHessian_eq_fderiv_fderiv hddφ]
  conv_rhs => rw [euclidean_eq_sum_single u, map_sum, sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, smul_apply]
  change _ = u i * (fderiv ℝ (fderiv ℝ φ) x (EuclideanSpace.single i 1)) v
  conv_rhs => arg 2; rw [euclidean_eq_sum_single v, map_sum]
  simp only [map_smul, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The curvature term in the integrated Bochner identity is nonnegative for a convex potential. -/
theorem hessianGradientForm_nonneg_of_convex {φ : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hconv : ConvexOn ℝ univ φ) (g : Space n → ℝ) (x : Space n) :
    0 ≤ hessianGradientForm φ g x := by
  unfold hessianGradientForm
  simp_rw [coordinateDerivative_eq_gradient]
  rw [coordinateHessian_quadratic_eq hφ]
  exact secondFrechet_nonneg_of_convex hφ hconv x (gradient g x)

/-- The genuine coordinate Hessian is positive semidefinite for a C² convex potential. -/
theorem coordinateHessian_posSemidef_of_convex {φ : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hconv : ConvexOn ℝ univ φ) (x : Space n) :
    (coordinateHessian φ x).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact Matrix.isHermitian_iff_isSymm.mpr (coordinateHessian_symmetric hφ x)
  · intro w
    have heq : star w ⬝ᵥ (coordinateHessian φ x *ᵥ w) =
        ∑ i : Fin n, ∑ j : Fin n, coordinateHessian φ x i j * w i * w j := by
      simp only [star_trivial, dotProduct, Matrix.mulVec, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [heq]
    change 0 ≤ ∑ i : Fin n, ∑ j : Fin n,
      coordinateHessian φ x i j * (WithLp.toLp 2 w : Space n) i * (WithLp.toLp 2 w : Space n) j
    rw [coordinateHessian_quadratic_eq hφ]
    exact secondFrechet_nonneg_of_convex hφ hconv x _

lemma hessianSquare_nonneg (g : Space n → ℝ) (x : Space n) : 0 ≤ hessianSquare g x := by
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

/-- The curvature integral is bounded by squared diffusion for every smooth compact test. -/
theorem integral_hessianGradientForm_le_diffusion_sq {φ g : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hg : ContDiff ℝ 3 g) (hc : HasCompactSupport g) :
    (∫ x, hessianGradientForm φ g x ∂potentialMeasure φ) ≤
      ∫ x, (weightedDiffusion φ g x) ^ 2 ∂potentialMeasure φ := by
  rw [integral_weightedDiffusion_sq_of_hasCompactSupport hφ hg hc]
  exact le_add_of_nonneg_left (integral_nonneg (hessianSquare_nonneg g))

/-- For a convex potential, the Hessian square is also controlled by squared diffusion. -/
theorem integral_hessianSquare_le_diffusion_sq {φ g : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hconv : ConvexOn ℝ univ φ)
    (hg : ContDiff ℝ 3 g) (hc : HasCompactSupport g) :
    (∫ x, hessianSquare g x ∂potentialMeasure φ) ≤
      ∫ x, (weightedDiffusion φ g x) ^ 2 ∂potentialMeasure φ := by
  rw [integral_weightedDiffusion_sq_of_hasCompactSupport hφ hg hc]
  exact le_add_of_nonneg_right
    (integral_nonneg (hessianGradientForm_nonneg_of_convex hφ hconv g))

end KLS
end

#print axioms KLS.secondFrechet_nonneg_of_convex
#print axioms KLS.coordinateHessian_quadratic_eq
#print axioms KLS.hessianGradientForm_nonneg_of_convex

#print axioms KLS.coordinateHessian_posSemidef_of_convex
#print axioms KLS.integral_hessianGradientForm_le_diffusion_sq
#print axioms KLS.integral_hessianSquare_le_diffusion_sq

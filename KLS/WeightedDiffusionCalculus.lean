import KLS.WeightedDiffusion

/-!
# Calculus of the concrete weighted diffusion

The coordinate Hessian is identified with the second Fréchet derivative,
its trace with mathlib's Laplacian, and its mixed coordinates with each
other under explicit smoothness. These facts use actual derivatives.
-/

open MeasureTheory InnerProductSpace
open scoped BigOperators Laplacian ContDiff

noncomputable section
namespace KLS

variable {n : ℕ}

lemma coordinateHessian_eq_fderiv_fderiv {g : Space n → ℝ} {x : Space n}
    (hg : DifferentiableAt ℝ (fderiv ℝ g) x) (i j : Fin n) :
    coordinateHessian g x i j =
      fderiv ℝ (fderiv ℝ g) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  unfold coordinateHessian coordinateDerivative
  rw [fderiv_clm_apply hg (differentiableAt_const _)]
  simp

lemma contDiff_coordinateDerivative {g : Space n → ℝ} {k m : ℕ∞ω}
    (hg : ContDiff ℝ k g) (hm : m + 1 ≤ k) (i : Fin n) :
    ContDiff ℝ m (coordinateDerivative g i) :=
  (hg.fderiv_right hm).clm_apply contDiff_const

lemma coordinateHessian_symmetric {g : Space n → ℝ} (hg : ContDiff ℝ 2 g)
    (x : Space n) : (coordinateHessian g x).IsSymm := by
  have hgd : DifferentiableAt ℝ (fderiv ℝ g) x :=
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) x
  apply Matrix.IsSymm.ext
  intro i j
  rw [coordinateHessian_eq_fderiv_fderiv hgd,
    coordinateHessian_eq_fderiv_fderiv hgd]
  exact (hg.contDiffAt.isSymmSndFDerivAt (by norm_num)).eq _ _

/-- The actual coordinate trace is the standard basis-independent Laplacian. -/
lemma coordinateLaplacian_eq_laplacian {g : Space n → ℝ} (hg : ContDiff ℝ 2 g)
    (x : Space n) : coordinateLaplacian g x = (Δ g) x := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis g
    (EuclideanSpace.basisFun (Fin n) ℝ)]
  unfold coordinateLaplacian
  apply Finset.sum_congr rfl
  intro i _
  have hgd : DifferentiableAt ℝ (fderiv ℝ g) x :=
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) x
  rw [coordinateHessian_eq_fderiv_fderiv hgd, iteratedFDeriv_two_apply]
  simp [EuclideanSpace.basisFun_apply]

/-- Literal agreement with `Δg - ⟨∇φ, ∇g⟩`. -/
lemma weightedDiffusion_eq_laplacian {φ g : Space n → ℝ} (hg : ContDiff ℝ 2 g)
    (x : Space n) : weightedDiffusion φ g x = (Δ g) x -
      inner ℝ (gradient φ x) (gradient g x) := by
  rw [weightedDiffusion, coordinateLaplacian_eq_laplacian hg]

/-- Weighted integration by parts stated with mathlib's standard Laplacian. -/
theorem integral_mul_laplacian_sub_inner_gradient {φ f g : Space n → ℝ}
    (hφ : Differentiable ℝ φ) (hf : Differentiable ℝ f) (hg : ContDiff ℝ 2 g)
    (h : DiffusionIntegrability φ f g) :
    (∫ x, f x * ((Δ g) x - inner ℝ (gradient φ x) (gradient g x)) ∂potentialMeasure φ) =
      -(∫ x, inner ℝ (gradient f x) (gradient g x) ∂potentialMeasure φ) := by
  simp_rw [← weightedDiffusion_eq_laplacian hg]
  exact integral_mul_weightedDiffusion hφ hf
    (fun i => (contDiff_coordinateDerivative hg (m := 1) (by norm_num) i).differentiable
      (by norm_num)) h

end KLS
end

#print axioms KLS.coordinateHessian_eq_fderiv_fderiv
#print axioms KLS.coordinateHessian_symmetric
#print axioms KLS.coordinateLaplacian_eq_laplacian
#print axioms KLS.weightedDiffusion_eq_laplacian

#print axioms KLS.integral_mul_laplacian_sub_inner_gradient

import KLS.GradientCompositionCalculus
import KLS.MatrixLogDetSecond

/-!
# The actual Hessian evolution equation

Starting from a C⁴ potential, a C² target potential, a positive definite
Hessian and the pointwise Monge–Ampère identity, this file derives the
Hessian evolution equation. Existence of such potentials is not asserted.
-/

open InnerProductSpace Matrix
open scoped BigOperators ContDiff Matrix.Norms.Elementwise

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS

variable {n : ℕ}

/-- An actual coordinate derivative of the actual Hessian matrix. -/
def hessianDerivative (φ : Space n → ℝ) (x : Space n) (i : Fin n) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun a b => coordinateDerivative (fun y => coordinateHessian φ y a b) i x

/-- The actual inverse-Hessian diffusion, with the target potential drift. -/
def hessianMetricDiffusion (φ V f : Space n → ℝ) (x : Space n) : ℝ :=
  (∑ a, ∑ b, (coordinateHessian φ x)⁻¹ a b * coordinateHessian f x a b) -
    ∑ a, coordinateDerivative V a (gradient φ x) * coordinateDerivative f a x

lemma contDiff_coordinateHessian_matrix {φ : Space n → ℝ} (hφ : ContDiff ℝ 4 φ) :
    ContDiff ℝ 2 (coordinateHessian φ) := by
  apply contDiff_pi.mpr
  intro a
  apply contDiff_pi.mpr
  intro b
  exact contDiff_coordinateHessian hφ (by norm_num) a b

lemma fderiv_coordinateHessian_apply {φ : Space n → ℝ} (hφ : ContDiff ℝ 4 φ)
    (x : Space n) (i : Fin n) :
    fderiv ℝ (coordinateHessian φ) x (EuclideanSpace.single i 1) =
      hessianDerivative φ x i := by
  ext a b
  exact (MatrixCalculus.fderiv_matrix_entry
    ((contDiff_coordinateHessian_matrix hφ).differentiable (by norm_num) x)
    a b (EuclideanSpace.single i 1)).symm

lemma fderiv_fderiv_coordinateHessian_apply {φ : Space n → ℝ} (hφ : ContDiff ℝ 4 φ)
    (x : Space n) (i j : Fin n) :
    fderiv ℝ (fun y => fderiv ℝ (coordinateHessian φ) y (EuclideanSpace.single j 1)) x
      (EuclideanSpace.single i 1) =
      fun a b => coordinateHessian (fun y => coordinateHessian φ y a b) x i j := by
  have hH := contDiff_coordinateHessian_matrix hφ
  have hDj : ContDiff ℝ 1
      (fun y => fderiv ℝ (coordinateHessian φ) y (EuclideanSpace.single j 1)) :=
    (hH.fderiv_right (by norm_num)).clm_apply contDiff_const
  ext a b
  rw [← MatrixCalculus.fderiv_matrix_entry (hDj.differentiable (by norm_num) x)]
  have heq : (fun y => (fderiv ℝ (coordinateHessian φ) y (EuclideanSpace.single j 1)) a b) =
      coordinateDerivative (fun y => coordinateHessian φ y a b) j := by
    funext y
    exact congrArg (fun M => M a b) (fderiv_coordinateHessian_apply hφ y j)
  rw [heq]
  rfl

lemma coordinateHessian_sub {f g : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : Space n) (i j : Fin n) :
    coordinateHessian (fun y => f y - g y) x i j =
      coordinateHessian f x i j - coordinateHessian g x i j := by
  have heq : coordinateDerivative (fun y => f y - g y) j =
      fun y => coordinateDerivative f j y - coordinateDerivative g j y := by
    funext y
    exact coordinateDerivative_sub (hf.differentiable (by norm_num) y)
      (hg.differentiable (by norm_num) y) j
  change coordinateDerivative (coordinateDerivative (fun y => f y - g y) j) i x = _
  rw [heq]
  exact coordinateDerivative_sub
    ((contDiff_coordinateDerivative hf (m := 1) (by norm_num) j).differentiable (by norm_num) x)
    ((contDiff_coordinateDerivative hg (m := 1) (by norm_num) j).differentiable (by norm_num) x) i

lemma trace_mul_hessian_eq_sum {f : Space n → ℝ} (hf : ContDiff ℝ 2 f)
    (J : Matrix (Fin n) (Fin n) ℝ) (x : Space n) :
    (J * coordinateHessian f x).trace =
      ∑ a, ∑ b, J a b * coordinateHessian f x a b := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [(coordinateHessian_symmetric hf x).apply a b]

lemma hessian_sandwich_eq_sum {φ V : Space n → ℝ} (hφ : ContDiff ℝ 2 φ)
    (x : Space n) (i j : Fin n) :
    (coordinateHessian φ x * coordinateHessian V (gradient φ x) * coordinateHessian φ x) i j =
      ∑ a, ∑ b, coordinateHessian V (gradient φ x) a b *
        coordinateHessian φ x i a * coordinateHessian φ x j b := by
  simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [(coordinateHessian_symmetric hφ x).apply j b]
  ring

/-- Twice differentiating the pointwise Monge–Ampère identity gives the
actual Hessian evolution, including the positive third-derivative contraction.
The equation, regularity and definiteness hypotheses are all explicit. -/
theorem hessianMetricDiffusion_hessian {φ V : Space n → ℝ}
    (hφ : ContDiff ℝ 4 φ) (hV : ContDiff ℝ 2 V)
    (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    (hMA : ∀ x, Real.log (coordinateHessian φ x).det = -φ x + V (gradient φ x))
    (x : Space n) (i j : Fin n) :
    hessianMetricDiffusion φ V (fun y => coordinateHessian φ y i j) x +
      coordinateHessian φ x i j =
      (coordinateHessian φ x * coordinateHessian V (gradient φ x) * coordinateHessian φ x) i j +
      ((coordinateHessian φ x)⁻¹ * hessianDerivative φ x i *
        (coordinateHessian φ x)⁻¹ * hessianDerivative φ x j).trace := by
  have hφ3 : ContDiff ℝ 3 φ := hφ.of_le (by norm_num)
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by norm_num)
  have hH := contDiff_coordinateHessian_matrix hφ
  have hlog := MatrixCalculus.fderiv_fderiv_logDet_comp_apply_posDef hH (hpos x)
    (EuclideanSpace.single j 1) (EuclideanSpace.single i 1)
  change coordinateHessian (fun y => Real.log (coordinateHessian φ y).det) x i j = _ at hlog
  rw [fderiv_fderiv_coordinateHessian_apply hφ,
    fderiv_coordinateHessian_apply hφ, fderiv_coordinateHessian_apply hφ] at hlog
  have hfourth : (fun a b => coordinateHessian (fun y => coordinateHessian φ y a b) x i j) =
      coordinateHessian (fun y => coordinateHessian φ y i j) x := by
    funext a b
    exact coordinateHessian_hessian_exchange hφ i j a b x
  rw [hfourth, trace_mul_hessian_eq_sum (contDiff_coordinateHessian hφ (by norm_num) i j)] at hlog
  have hfun : (fun y => Real.log (coordinateHessian φ y).det) =
      fun y => V (gradient φ y) - φ y := by
    funext y
    rw [hMA]
    ring
  rw [hfun, coordinateHessian_sub
    (f := fun y => V (gradient φ y)) (g := φ)
    (hV.comp (contDiff_gradient hφ3 (by norm_num))) hφ2,
    coordinateHessian_comp_gradient hV hφ3,
    ← hessian_sandwich_eq_sum hφ2] at hlog
  unfold hessianMetricDiffusion
  linarith

lemma hessianDerivative_symmetric {φ : Space n → ℝ} (hφ : ContDiff ℝ 2 φ)
    (x : Space n) (i : Fin n) : (hessianDerivative φ x i).IsSymm := by
  apply Matrix.IsSymm.ext
  intro a b
  unfold hessianDerivative
  congr 1
  funext y
  exact (coordinateHessian_symmetric hφ y).apply a b

/-- The matrix trace is precisely the four-index contraction. -/
lemma trace_inverse_hessian_contraction (J T U : Matrix (Fin n) (Fin n) ℝ)
    (hJ : J.IsSymm) (hU : U.IsSymm) :
    (J * T * J * U).trace =
      ∑ a, ∑ b, ∑ c, ∑ d, J a c * J b d * T a b * U c d := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Finset.sum_mul]
  conv_lhs =>
    arg 2
    ext p
    arg 2
    ext q
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext p
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext a
    arg 2
    ext p
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext a
    rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  rw [hJ.apply a c, hU.apply c d]
  ring

/-- The literal coordinate form of the Hessian evolution equation. -/
theorem hessianMetricDiffusion_hessian_expanded {φ V : Space n → ℝ}
    (hφ : ContDiff ℝ 4 φ) (hV : ContDiff ℝ 2 V)
    (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    (hMA : ∀ x, Real.log (coordinateHessian φ x).det = -φ x + V (gradient φ x))
    (x : Space n) (i j : Fin n) :
    hessianMetricDiffusion φ V (fun y => coordinateHessian φ y i j) x +
      coordinateHessian φ x i j =
      (coordinateHessian φ x * coordinateHessian V (gradient φ x) * coordinateHessian φ x) i j +
      ∑ a, ∑ b, ∑ c, ∑ d,
        (coordinateHessian φ x)⁻¹ a c * (coordinateHessian φ x)⁻¹ b d *
          coordinateDerivative (fun y => coordinateHessian φ y a b) i x *
          coordinateDerivative (fun y => coordinateHessian φ y c d) j x := by
  rw [hessianMetricDiffusion_hessian hφ hV hpos hMA,
    trace_inverse_hessian_contraction _ _ _
      (coordinateHessian_symmetric (hφ.of_le (by norm_num)) x).inv
      (hessianDerivative_symmetric (hφ.of_le (by norm_num)) x j)]
  rfl

end KLS
end

#print axioms KLS.fderiv_fderiv_coordinateHessian_apply
#print axioms KLS.hessianMetricDiffusion_hessian
#print axioms KLS.hessianMetricDiffusion_hessian_expanded

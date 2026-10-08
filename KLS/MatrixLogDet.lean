import KLS.Definitions
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Derivatives of the genuine matrix log determinant

The determinant differential is derived from the polynomial coefficient
identity at the identity matrix, then transported to invertible matrices by
actual multiplication and inversion. No Jacobi formula is assumed.
-/

open Matrix Polynomial
open scoped BigOperators Matrix.Norms.Elementwise

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS.MatrixCalculus

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem contDiff_det : ContDiff ℝ ⊤ (Matrix.det : Matrix ι ι ℝ → ℝ) := by
  change ContDiff ℝ ⊤ (fun A : Matrix ι ι ℝ => A.det)
  simp_rw [Matrix.det_apply']
  fun_prop

/-- The polynomial trace identity gives the analytic derivative at the identity. -/
theorem hasDerivAt_det_one_add_smul (B : Matrix ι ι ℝ) :
    HasDerivAt (fun t : ℝ => (1 + t • B).det) B.trace 0 := by
  let p : ℝ[X] := Matrix.det (1 + (X : ℝ[X]) • B.map C)
  have heval (t : ℝ) : p.eval t = (1 + t • B).det := by
    change (Polynomial.evalRingHom t) (Matrix.det (1 + (X : ℝ[X]) • B.map C)) = _
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp [RingHom.mapMatrix_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply,
      Matrix.one_apply, smul_eq_mul, Polynomial.evalRingHom]
    split_ifs <;> simp [mul_comm]
  have h := p.hasDerivAt 0
  have hp : p.derivative.eval 0 = B.trace := Matrix.derivative_det_one_add_X_smul B
  simpa only [heval, hp] using h

/-- The determinant derivative along an arbitrary matrix direction. -/
theorem hasDerivAt_det_add_smul (A B : Matrix ι ι ℝ) (hA : A.det ≠ 0) :
    HasDerivAt (fun t : ℝ => (A + t • B).det) (A.det * (A⁻¹ * B).trace) 0 := by
  have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  have hfactor (t : ℝ) : A + t • B = A * (1 + t • (A⁻¹ * B)) := by
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul,
      Matrix.mul_nonsing_inv_cancel_left A B hu]
  have h := (hasDerivAt_det_one_add_smul (A⁻¹ * B)).const_mul A.det
  simpa only [← Matrix.det_mul, ← hfactor] using h

/-- Jacobi's formula for the actual Fréchet derivative, evaluated at a direction. -/
theorem fderiv_det_apply (A B : Matrix ι ι ℝ) (hA : A.det ≠ 0) :
    fderiv ℝ Matrix.det A B = A.det * (A⁻¹ * B).trace := by
  have hdet : DifferentiableAt ℝ (Matrix.det : Matrix ι ι ℝ → ℝ) A :=
    contDiff_det.differentiable (by simp) A
  have hline : HasDerivAt (fun t : ℝ => A + t • B) B 0 := by
    simpa only [one_smul, id_eq] using ((hasDerivAt_id (0 : ℝ)).smul_const B).const_add A
  have hd0 : HasFDerivAt Matrix.det (fderiv ℝ Matrix.det A) (A + (0 : ℝ) • B) := by
    simpa only [zero_smul, add_zero] using hdet.hasFDerivAt
  have h := hd0.comp_hasDerivAt 0 hline
  simpa only [zero_smul, add_zero] using h.unique (hasDerivAt_det_add_smul A B hA)

def logDet (A : Matrix ι ι ℝ) : ℝ := Real.log A.det

theorem differentiableAt_logDet (A : Matrix ι ι ℝ) (hA : A.det ≠ 0) :
    DifferentiableAt ℝ logDet A :=
  (contDiff_det.differentiable (by simp) A).log hA

/-- The actual matrix log-determinant differential; positive definiteness is
sufficient, but invertibility already gives this local identity. -/
theorem fderiv_logDet_apply (A B : Matrix ι ι ℝ) (hA : A.det ≠ 0) :
    fderiv ℝ logDet A B = (A⁻¹ * B).trace := by
  have hdet : DifferentiableAt ℝ (Matrix.det : Matrix ι ι ℝ → ℝ) A :=
    contDiff_det.differentiable (by simp) A
  change fderiv ℝ (fun M : Matrix ι ι ℝ => Real.log M.det) A B = _
  rw [(hdet.hasFDerivAt.log hA).fderiv]
  simp only [_root_.smul_apply, smul_eq_mul, fderiv_det_apply A B hA]
  field_simp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Chain rule for a genuinely differentiable matrix field. -/
theorem fderiv_logDet_comp_apply {A : E → Matrix ι ι ℝ} {x : E}
    (hA : DifferentiableAt ℝ A x) (hdet : (A x).det ≠ 0) (v : E) :
    fderiv ℝ (fun y => logDet (A y)) x v = ((A x)⁻¹ * fderiv ℝ A x v).trace := by
  change fderiv ℝ (logDet ∘ A) x v = _
  rw [(differentiableAt_logDet (A x) hdet).hasFDerivAt.comp x hA.hasFDerivAt |>.fderiv]
  exact fderiv_logDet_apply _ _ hdet

/-- The positive-definite specialization has no separately assumed determinant sign. -/
theorem fderiv_logDet_comp_apply_posDef {A : E → Matrix ι ι ℝ} {x : E}
    (hA : DifferentiableAt ℝ A x) (hpos : (A x).PosDef) (v : E) :
    fderiv ℝ (fun y => Real.log (A y).det) x v =
      ((A x)⁻¹ * fderiv ℝ A x v).trace :=
  fderiv_logDet_comp_apply hA hpos.det_pos.ne' v

end KLS.MatrixCalculus
end

#print axioms KLS.MatrixCalculus.hasDerivAt_det_add_smul
#print axioms KLS.MatrixCalculus.fderiv_det_apply
#print axioms KLS.MatrixCalculus.fderiv_logDet_comp_apply_posDef

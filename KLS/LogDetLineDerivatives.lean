import KLS.MatrixLogDetSecond

open Matrix
open scoped BigOperators Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

theorem hasDerivAt_matrix_logDet {A : ℝ → Matrix (Fin n) (Fin n) ℝ}
    {D : Matrix (Fin n) (Fin n) ℝ} {t : ℝ}
    (hA : HasDerivAt A D t) (hdet : (A t).det ≠ 0) :
    HasDerivAt (fun s => Real.log (A s).det) ((A t)⁻¹ * D).trace t := by
  have hd := (MatrixCalculus.differentiableAt_logDet (A t) hdet).comp t hA.differentiableAt
  have hd' : DifferentiableAt ℝ (fun s => Real.log (A s).det) t := hd
  have he : deriv (fun s => Real.log (A s).det) t = ((A t)⁻¹ * D).trace := by
    change fderiv ℝ (fun s => MatrixCalculus.logDet (A s)) t 1 = _
    rw [MatrixCalculus.fderiv_logDet_comp_apply hA.differentiableAt hdet,
      fderiv_apply_one_eq_deriv, hA.deriv]
  simpa only [he] using hd'.hasDerivAt

theorem hasDerivAt_trace_matrix_inv_mul {A : ℝ → Matrix (Fin n) (Fin n) ℝ}
    {D : Matrix (Fin n) (Fin n) ℝ} {t : ℝ}
    (hA : HasDerivAt A D t) (hdet : (A t).det ≠ 0)
    (X : Matrix (Fin n) (Fin n) ℝ) :
    HasDerivAt (fun s => ((A s)⁻¹ * X).trace) (-((A t)⁻¹ * D * (A t)⁻¹ * X).trace) t := by
  have hInv : DifferentiableAt ℝ (fun s => (A s)⁻¹) t :=
    (MatrixCalculus.differentiableAt_matrix_inv (A t) hdet).comp t hA.differentiableAt
  have hP := MatrixCalculus.differentiableAt_matrix_mul hInv (differentiableAt_const (c := X))
  have hTr : DifferentiableAt ℝ (fun s => ((A s)⁻¹ * X).trace) t := by
    change DifferentiableAt ℝ (fun s => ∑ i, ((A s)⁻¹ * X) i i) t
    exact DifferentiableAt.fun_sum (u := Finset.univ) fun i _ =>
      MatrixCalculus.differentiableAt_matrix_entry hP i i
  have he : deriv (fun s => ((A s)⁻¹ * X).trace) t = -((A t)⁻¹ * D * (A t)⁻¹ * X).trace := by
    change fderiv ℝ (fun s => ((A s)⁻¹ * X).trace) t 1 = _
    rw [MatrixCalculus.fderiv_trace_apply hP,
      MatrixCalculus.fderiv_matrix_mul_apply hInv (differentiableAt_const (c := X)),
      MatrixCalculus.fderiv_matrix_inv_comp_apply hA.differentiableAt hdet]
    simp only [fderiv_fun_const, Pi.zero_apply, _root_.zero_apply, Matrix.mul_zero, add_zero,
      Matrix.neg_mul, Matrix.trace_neg, fderiv_apply_one_eq_deriv, hA.deriv]
  simpa only [he] using hTr.hasDerivAt

end KLS
end

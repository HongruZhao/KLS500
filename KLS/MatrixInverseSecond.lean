import KLS.TensorMatrixDifferential

/-! Genuine second Fréchet derivative of matrix inversion, using the local
inverse identity already proved for the actual nonsingular inverse. -/
open Matrix Filter
open scoped BigOperators Matrix.Norms.Elementwise Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS.MatrixCalculus
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fderiv_fderiv_matrix_inv_apply {A : E → Matrix ι ι ℝ} {x : E}
    (hA : Differentiable ℝ A) (v w : E)
    (hAv : DifferentiableAt ℝ (fun y => fderiv ℝ A y v) x) (hdet : (A x).det ≠ 0) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => (A z)⁻¹) y v) x w =
      (A x)⁻¹ * fderiv ℝ A x w * (A x)⁻¹ * fderiv ℝ A x v * (A x)⁻¹ +
      (A x)⁻¹ * fderiv ℝ A x v * (A x)⁻¹ * fderiv ℝ A x w * (A x)⁻¹ -
      (A x)⁻¹ * fderiv ℝ (fun y => fderiv ℝ A y v) x w * (A x)⁻¹ := by
  have hInv : DifferentiableAt ℝ (fun y => (A y)⁻¹) x :=
    (differentiableAt_matrix_inv (A x) hdet).comp x (hA x)
  have heq : (fun y => fderiv ℝ (fun z => (A z)⁻¹) y v) =ᶠ[𝓝 x]
      fun y => -((A y)⁻¹ * fderiv ℝ A y v * (A y)⁻¹) := by
    have hn : ∀ᶠ y in 𝓝 x, (A y).det ≠ 0 :=
      (contDiff_det.continuous.continuousAt.comp (hA x).continuousAt).eventually_ne hdet
    filter_upwards [hn] with y hy
    exact fderiv_matrix_inv_comp_apply (hA y) hy v
  have hProd := differentiableAt_matrix_mul hInv hAv
  rw [heq.fderiv_eq, fderiv_fun_neg]
  simp only [ContinuousLinearMap.neg_apply]
  rw [fderiv_matrix_mul_apply hProd hInv, fderiv_matrix_mul_apply hInv hAv,
    fderiv_matrix_inv_comp_apply (hA x) hdet]
  noncomm_ring

/-- Identity-point specialization with arbitrary first and second derivatives. -/
theorem fderiv_fderiv_matrix_inv_at_identity {A : E → Matrix ι ι ℝ} {x : E}
    (hA : Differentiable ℝ A) (v : E)
    (hAv : DifferentiableAt ℝ (fun y => fderiv ℝ A y v) x) (hI : A x = 1) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => (A z)⁻¹) y v) x v =
      2 • (fderiv ℝ A x v * fderiv ℝ A x v) -
      fderiv ℝ (fun y => fderiv ℝ A y v) x v := by
  have hdet : (A x).det ≠ 0 := by simp [hI]
  rw [fderiv_fderiv_matrix_inv_apply hA v v hAv hdet, hI]
  simp [two_smul]

end KLS.MatrixCalculus
end
#print axioms KLS.MatrixCalculus.fderiv_fderiv_matrix_inv_apply

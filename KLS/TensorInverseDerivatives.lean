import KLS.TensorMatrixSecond

/-! Genuine first and second derivatives of the full tensor inverse metric
at identity, including second derivatives of its matrix argument. -/
open Matrix
open scoped BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS.TensorEnergy
open KLS.MatrixCalculus
variable {n r : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The sum of all one-slot matrix actions. -/
def tensorSlotSum (H : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin r → Fin n) (Fin r → Fin n) ℝ := ∑ s, tensorSlot s H

theorem tensorSlot_sub (s : Fin r) (H K : Matrix (Fin n) (Fin n) ℝ) :
    tensorSlot s (H-K) = tensorSlot s H - tensorSlot s K := by
  simp [sub_eq_add_neg, tensorSlot_add, tensorSlot_neg]

theorem tensorSlotSum_one : tensorSlotSum (r := r) (1 : Matrix (Fin n) (Fin n) ℝ) = r • 1 := by
  simp [tensorSlotSum, tensorSlot_one]

theorem tensorSlotSum_add (H K : Matrix (Fin n) (Fin n) ℝ) :
    tensorSlotSum (r := r) (H+K) = tensorSlotSum H + tensorSlotSum K := by
  simp [tensorSlotSum, tensorSlot_add, Finset.sum_add_distrib]

theorem tensorSlotSum_neg (H : Matrix (Fin n) (Fin n) ℝ) :
    tensorSlotSum (r := r) (-H) = -tensorSlotSum H := by
  simp [tensorSlotSum, tensorSlot_neg]

theorem differentiableAt_inverse_directional_derivative
    {A : E → Matrix (Fin n) (Fin n) ℝ} {x : E}
    (hA : Differentiable ℝ A) (hdet : ∀ y, (A y).det ≠ 0) (v : E)
    (hAv : DifferentiableAt ℝ (fun y => fderiv ℝ A y v) x) :
    DifferentiableAt ℝ (fun y => fderiv ℝ (fun z => (A z)⁻¹) y v) x := by
  have hEq : (fun y => fderiv ℝ (fun z => (A z)⁻¹) y v) =
      fun y => -((A y)⁻¹ * fderiv ℝ A y v * (A y)⁻¹) := by
    funext y
    exact fderiv_matrix_inv_comp_apply (hA y) (hdet y) v
  rw [hEq]
  have hInv : DifferentiableAt ℝ (fun y => (A y)⁻¹) x :=
    (differentiableAt_matrix_inv (A x) (hdet x)).comp x (hA x)
  exact (differentiableAt_matrix_mul (differentiableAt_matrix_mul hInv hAv) hInv).neg

theorem fderiv_tensorInverse_at_identity {A : E → Matrix (Fin n) (Fin n) ℝ} {x : E}
    (hA : DifferentiableAt ℝ A x) (hI : A x = 1) (v : E) :
    fderiv ℝ (fun y => tensorMatrix (r := r) (A y)⁻¹) x v =
      -tensorSlotSum (fderiv ℝ A x v) := by
  have hdet : (A x).det ≠ 0 := by simp [hI]
  have hInv : DifferentiableAt ℝ (fun y => (A y)⁻¹) x :=
    (differentiableAt_matrix_inv (A x) hdet).comp x hA
  change fderiv ℝ (fun y => tensorMatrixFamily (fun _ : Fin r => (A y)⁻¹)) x v = _
  rw [fderiv_tensorMatrixFamily_identity (fun _ => hInv) (fun _ => by simp [hI])]
  simp only [fderiv_matrix_inv_comp_apply hA hdet, hI, inv_one,
    Matrix.one_mul, Matrix.mul_one, tensorSlot_neg, Finset.sum_neg_distrib, tensorSlotSum]

theorem sum_twice_diagonal_add_offdiagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ : Type*} [Fintype κ] (M : ι → Matrix κ κ ℝ) :
    (∑ s, (M s * M s + M s * M s + ∑ t ∈ Finset.univ.erase s, M s * M t)) =
      (∑ s, M s) * (∑ s, M s) + ∑ s, M s * M s := by
  calc
    _ = ∑ s, ((∑ t, M s * M t) + M s * M s) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s)]
      abel
    _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_mul]; simp_rw [Finset.mul_sum]

/-- This proves the second derivative underlying paper (87); the final term
retains curvature of a nonlinear matrix field. -/
theorem fderiv_fderiv_tensorInverse_at_identity
    {A : E → Matrix (Fin n) (Fin n) ℝ} {x : E}
    (hA : Differentiable ℝ A) (hdet : ∀ y, (A y).det ≠ 0) (v : E)
    (hAv : DifferentiableAt ℝ (fun y => fderiv ℝ A y v) x) (hI : A x = 1) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => tensorMatrix (r := r) (A z)⁻¹) y v) x v =
      tensorSlotSum (fderiv ℝ A x v) * tensorSlotSum (fderiv ℝ A x v) +
      ∑ s, tensorSlot s (fderiv ℝ A x v) * tensorSlot s (fderiv ℝ A x v) -
      tensorSlotSum (fderiv ℝ (fun y => fderiv ℝ A y v) x v) := by
  have hInv : Differentiable ℝ (fun y => (A y)⁻¹) := fun y =>
    (differentiableAt_matrix_inv (A y) (hdet y)).comp y (hA y)
  have hInvv := differentiableAt_inverse_directional_derivative hA hdet v hAv
  change fderiv ℝ (fun y => fderiv ℝ (fun z => tensorMatrixFamily (fun _ : Fin r => (A z)⁻¹)) y v) x v = _
  rw [fderiv_fderiv_tensorMatrixFamily_identity (fun _ => hInv) v v (fun _ => hInvv) (fun _ => by simp [hI])]
  simp only [fderiv_fderiv_matrix_inv_at_identity hA v hAv hI,
    fderiv_matrix_inv_comp_apply (hA x) (hdet x), hI, inv_one,
    Matrix.one_mul, Matrix.mul_one, tensorSlot_sub, tensorSlot_neg, neg_mul_neg,
    two_smul, tensorSlot_add, tensorSlot_mul]
  simp_rw [sub_add_eq_add_sub]
  rw [Finset.sum_sub_distrib, sum_twice_diagonal_add_offdiagonal]
  rfl

end KLS.TensorEnergy
end
#print axioms KLS.TensorEnergy.fderiv_fderiv_tensorInverse_at_identity

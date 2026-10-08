import KLS.MatrixLogDet

/-!
# The inverse differential and second matrix log-determinant derivative

Matrix inversion is differentiated through its actual adjugate formula and
the locally valid identity `A * A⁻¹ = 1`. The second log-determinant formula
therefore uses the actual inverse and actual iterated Fréchet derivatives.
-/

open Matrix Filter
open scoped BigOperators Matrix.Norms.Elementwise Topology

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS.MatrixCalculus

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem contDiff_adjugate : ContDiff ℝ ⊤ (Matrix.adjugate : Matrix ι ι ℝ → Matrix ι ι ℝ) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  simp_rw [Matrix.adjugate_apply]
  apply contDiff_det.comp
  change ContDiff ℝ ⊤ (fun M : Matrix ι ι ℝ => Function.update M j (Pi.single i 1))
  apply contDiff_pi.mpr
  intro k
  by_cases hkj : k = j
  · subst k
    simp only [Function.update_self]
    fun_prop
  · simp only [Function.update_of_ne hkj]
    fun_prop

theorem differentiableAt_matrix_inv (A : Matrix ι ι ℝ) (hA : A.det ≠ 0) :
    DifferentiableAt ℝ (fun M : Matrix ι ι ℝ => M⁻¹) A := by
  have hd : DifferentiableAt ℝ (Matrix.det : Matrix ι ι ℝ → ℝ) A :=
    contDiff_det.differentiable (by simp) A
  have ha : DifferentiableAt ℝ (Matrix.adjugate : Matrix ι ι ℝ → Matrix ι ι ℝ) A :=
    contDiff_adjugate.differentiable (by simp) A
  convert! (hd.inv hA).smul ha using 1
  funext M
  simp only [Matrix.inv_def, Ring.inverse_eq_inv']
  rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [DecidableEq ι] in
theorem differentiableAt_matrix_entry {A : E → Matrix ι ι ℝ} {x : E}
    (hA : DifferentiableAt ℝ A x) (i j : ι) :
    DifferentiableAt ℝ (fun y => A y i j) x :=
  differentiableAt_pi.mp (differentiableAt_pi.mp hA i) j

omit [DecidableEq ι] in
theorem fderiv_matrix_entry {A : E → Matrix ι ι ℝ} {x : E}
    (hA : DifferentiableAt ℝ A x) (i j : ι) (v : E) :
    fderiv ℝ (fun y => A y i j) x v = (fderiv ℝ A x v) i j := by
  rw [fderiv_apply (differentiableAt_pi.mp hA i) j, fderiv_apply hA i]
  rfl

omit [DecidableEq ι] in
theorem differentiableAt_matrix_mul {A B : E → Matrix ι ι ℝ} {x : E}
    (hA : DifferentiableAt ℝ A x) (hB : DifferentiableAt ℝ B x) :
    DifferentiableAt ℝ (fun y => A y * B y) x := by
  apply differentiableAt_pi.mpr
  intro i
  apply differentiableAt_pi.mpr
  intro j
  change DifferentiableAt ℝ (fun y => ∑ k, A y i k * B y k j) x
  exact DifferentiableAt.fun_sum (u := Finset.univ) fun k _ =>
    (differentiableAt_matrix_entry hA i k).mul (differentiableAt_matrix_entry hB k j)

theorem fderiv_matrix_mul_apply {A B : E → Matrix ι ι ℝ} {x : E}
    (hA : DifferentiableAt ℝ A x) (hB : DifferentiableAt ℝ B x) (v : E) :
    fderiv ℝ (fun y => A y * B y) x v = fderiv ℝ A x v * B x + A x * fderiv ℝ B x v := by
  ext i j
  rw [← fderiv_matrix_entry (differentiableAt_matrix_mul hA hB)]
  simp only [Matrix.mul_apply, Matrix.add_apply]
  rw [fderiv_fun_sum (u := Finset.univ) (A := fun k y => A y i k * B y k j) (fun k _ =>
    (differentiableAt_matrix_entry hA i k).mul (differentiableAt_matrix_entry hB k j))]
  simp only [_root_.sum_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [fderiv_fun_mul (differentiableAt_matrix_entry hA i k)
    (differentiableAt_matrix_entry hB k j)]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, fderiv_matrix_entry hA,
    fderiv_matrix_entry hB]
  ring

omit [DecidableEq ι] in
theorem fderiv_trace_apply {A : E → Matrix ι ι ℝ} {x : E}
    (hA : DifferentiableAt ℝ A x) (v : E) :
    fderiv ℝ (fun y => (A y).trace) x v = (fderiv ℝ A x v).trace := by
  simp only [Matrix.trace, Matrix.diag_apply]
  rw [fderiv_fun_sum (u := Finset.univ) (fun i _ => differentiableAt_matrix_entry hA i i)]
  simp only [_root_.sum_apply, fderiv_matrix_entry hA]

/-- Differentiating the genuine local inverse identity determines the inverse differential. -/
theorem fderiv_matrix_inv_apply (A B : Matrix ι ι ℝ) (hA : A.det ≠ 0) :
    fderiv ℝ (fun M : Matrix ι ι ℝ => M⁻¹) A B = -(A⁻¹ * B * A⁻¹) := by
  have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  have heq : (fun M : Matrix ι ι ℝ => M * M⁻¹) =ᶠ[𝓝 A] fun _ => 1 := by
    have hn : ∀ᶠ M : Matrix ι ι ℝ in 𝓝 A, M.det ≠ 0 :=
      (contDiff_det.continuous.continuousAt).eventually_ne hA
    filter_upwards [hn] with M hM
    exact Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hM)
  have hder : fderiv ℝ (fun M : Matrix ι ι ℝ => M * M⁻¹) A B = 0 := by
    rw [heq.fderiv_eq]
    simp
  have hcalc := fderiv_matrix_mul_apply (A := id) (B := fun M : Matrix ι ι ℝ => M⁻¹)
    (x := A) differentiableAt_id (differentiableAt_matrix_inv A hA) B
  simp only [id_eq, fderiv_id, ContinuousLinearMap.id_apply] at hcalc
  rw [hcalc] at hder
  have hmul := congrArg (fun M : Matrix ι ι ℝ => A⁻¹ * M) hder
  rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul A hu, Matrix.one_mul, Matrix.mul_zero] at hmul
  exact eq_neg_of_add_eq_zero_right hmul

theorem fderiv_matrix_inv_comp_apply {A : E → Matrix ι ι ℝ} {x : E}
    (hA : DifferentiableAt ℝ A x) (hdet : (A x).det ≠ 0) (v : E) :
    fderiv ℝ (fun y => (A y)⁻¹) x v = -((A x)⁻¹ * fderiv ℝ A x v * (A x)⁻¹) := by
  have h := (differentiableAt_matrix_inv (A x) hdet).hasFDerivAt.comp x hA.hasFDerivAt
  change fderiv ℝ ((fun M : Matrix ι ι ℝ => M⁻¹) ∘ A) x v = _
  rw [h.fderiv]
  exact fderiv_matrix_inv_apply _ _ hdet

/-- The second differential along a matrix field, with the actual first and
second differentiability hypotheses stated explicitly. -/
theorem fderiv_fderiv_logDet_comp_apply {A : E → Matrix ι ι ℝ} {x : E}
    (hA : Differentiable ℝ A) (v w : E)
    (hAv : DifferentiableAt ℝ (fun y => fderiv ℝ A y v) x) (hdet : (A x).det ≠ 0) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => logDet (A z)) y v) x w =
      ((A x)⁻¹ * fderiv ℝ (fun y => fderiv ℝ A y v) x w).trace -
        ((A x)⁻¹ * fderiv ℝ A x w * (A x)⁻¹ * fderiv ℝ A x v).trace := by
  have hInv : DifferentiableAt ℝ (fun y => (A y)⁻¹) x :=
    (differentiableAt_matrix_inv (A x) hdet).comp x (hA x)
  have heq : (fun y => fderiv ℝ (fun z => logDet (A z)) y v) =ᶠ[𝓝 x]
      fun y => ((A y)⁻¹ * fderiv ℝ A y v).trace := by
    have hn : ∀ᶠ y in 𝓝 x, (A y).det ≠ 0 :=
      (contDiff_det.continuous.continuousAt.comp (hA x).continuousAt).eventually_ne hdet
    filter_upwards [hn] with y hy
    exact fderiv_logDet_comp_apply (hA y) hy v
  rw [heq.fderiv_eq, fderiv_trace_apply (differentiableAt_matrix_mul hInv hAv),
    fderiv_matrix_mul_apply hInv hAv, fderiv_matrix_inv_comp_apply (hA x) hdet,
    Matrix.neg_mul, Matrix.trace_add, Matrix.trace_neg]
  ring

/-- For a C² matrix field, positive definiteness at the point supplies all
nondegeneracy and differentiability required by the genuine second derivative. -/
theorem fderiv_fderiv_logDet_comp_apply_posDef {A : E → Matrix ι ι ℝ} {x : E}
    (hA : ContDiff ℝ 2 A) (hpos : (A x).PosDef) (v w : E) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => Real.log (A z).det) y v) x w =
      ((A x)⁻¹ * fderiv ℝ (fun y => fderiv ℝ A y v) x w).trace -
        ((A x)⁻¹ * fderiv ℝ A x w * (A x)⁻¹ * fderiv ℝ A x v).trace := by
  have hDA : ContDiff ℝ 1 (fderiv ℝ A) := hA.fderiv_right (by norm_num)
  have hAv : DifferentiableAt ℝ (fun y => fderiv ℝ A y v) x :=
    (hDA.differentiable (by norm_num) x).clm_apply (differentiableAt_const v)
  exact fderiv_fderiv_logDet_comp_apply (hA.differentiable (by norm_num)) v w hAv hpos.det_pos.ne'

end KLS.MatrixCalculus
end

#print axioms KLS.MatrixCalculus.fderiv_matrix_mul_apply
#print axioms KLS.MatrixCalculus.fderiv_matrix_inv_apply
#print axioms KLS.MatrixCalculus.fderiv_fderiv_logDet_comp_apply_posDef

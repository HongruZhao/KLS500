import KLS.TensorInverseDerivatives

/-! Finite-coordinate product rules for genuine quadratic-form derivatives. -/
open Matrix
open scoped BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS.TensorEnergy
open KLS.MatrixCalculus
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fderiv_vector_entry {T : E → ι → ℝ} {x : E}
    (hT : DifferentiableAt ℝ T x) (i : ι) (v : E) :
    fderiv ℝ (fun y => T y i) x v = fderiv ℝ T x v i := by
  rw [fderiv_apply hT i]
  rfl

theorem differentiableAt_dotProduct {T U : E → ι → ℝ} {x : E}
    (hT : DifferentiableAt ℝ T x) (hU : DifferentiableAt ℝ U x) :
    DifferentiableAt ℝ (fun y => T y ⬝ᵥ U y) x := by
  exact DifferentiableAt.fun_sum (u := Finset.univ) fun i _ =>
    (differentiableAt_pi.mp hT i).mul (differentiableAt_pi.mp hU i)

theorem fderiv_dotProduct_apply {T U : E → ι → ℝ} {x : E}
    (hT : DifferentiableAt ℝ T x) (hU : DifferentiableAt ℝ U x) (v : E) :
    fderiv ℝ (fun y => T y ⬝ᵥ U y) x v =
      (fderiv ℝ T x v) ⬝ᵥ U x + T x ⬝ᵥ (fderiv ℝ U x v) := by
  unfold dotProduct
  rw [fderiv_fun_sum (u := Finset.univ) (A := fun i y => T y i * U y i) (fun i _ =>
    (differentiableAt_pi.mp hT i).mul (differentiableAt_pi.mp hU i))]
  simp only [_root_.sum_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [fderiv_fun_mul (differentiableAt_pi.mp hT i) (differentiableAt_pi.mp hU i)]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul,
    fderiv_vector_entry hT i, fderiv_vector_entry hU i]
  ring

theorem differentiableAt_mulVec {Q : E → Matrix ι ι ℝ} {T : E → ι → ℝ} {x : E}
    (hQ : DifferentiableAt ℝ Q x) (hT : DifferentiableAt ℝ T x) :
    DifferentiableAt ℝ (fun y => Q y *ᵥ T y) x := by
  apply differentiableAt_pi.mpr
  intro i
  exact differentiableAt_dotProduct (differentiableAt_pi.mp hQ i) hT

theorem fderiv_mulVec_apply {Q : E → Matrix ι ι ℝ} {T : E → ι → ℝ} {x : E}
    (hQ : DifferentiableAt ℝ Q x) (hT : DifferentiableAt ℝ T x) (v : E) :
    fderiv ℝ (fun y => Q y *ᵥ T y) x v =
      fderiv ℝ Q x v *ᵥ T x + Q x *ᵥ fderiv ℝ T x v := by
  funext i
  rw [← fderiv_vector_entry (differentiableAt_mulVec hQ hT) i v]
  change fderiv ℝ (fun y => (Q y i) ⬝ᵥ T y) x v = _
  rw [fderiv_dotProduct_apply (differentiableAt_pi.mp hQ i) hT v,
    fderiv_apply hQ i]
  rfl

theorem fderiv_quadratic_apply {Q : E → Matrix ι ι ℝ} {T : E → ι → ℝ} {x : E}
    (hQ : DifferentiableAt ℝ Q x) (hT : DifferentiableAt ℝ T x) (v : E) :
    fderiv ℝ (fun y => T y ⬝ᵥ (Q y *ᵥ T y)) x v =
      fderiv ℝ T x v ⬝ᵥ (Q x *ᵥ T x) +
      T x ⬝ᵥ (fderiv ℝ Q x v *ᵥ T x + Q x *ᵥ fderiv ℝ T x v) := by
  rw [fderiv_dotProduct_apply hT (differentiableAt_mulVec hQ hT) v,
    fderiv_mulVec_apply hQ hT v]

theorem fderiv_quadratic_at_identity {Q : E → Matrix ι ι ℝ} {T : E → ι → ℝ} {x : E}
    (hQ : DifferentiableAt ℝ Q x) (hT : DifferentiableAt ℝ T x) (hI : Q x = 1) (v : E) :
    fderiv ℝ (fun y => T y ⬝ᵥ (Q y *ᵥ T y)) x v =
      2 * (T x ⬝ᵥ fderiv ℝ T x v) + T x ⬝ᵥ (fderiv ℝ Q x v *ᵥ T x) := by
  rw [fderiv_quadratic_apply hQ hT v, hI]
  simp only [Matrix.one_mulVec, dotProduct_add]
  rw [dotProduct_comm (fderiv ℝ T x v) (T x)]
  ring

/-- The genuine second directional derivative, retaining all field curvature. -/
theorem fderiv_fderiv_quadratic_at_identity
    {Q : E → Matrix ι ι ℝ} {T : E → ι → ℝ} {x : E}
    (hQ : Differentiable ℝ Q) (hT : Differentiable ℝ T) (v : E)
    (hQv : DifferentiableAt ℝ (fun y => fderiv ℝ Q y v) x)
    (hTv : DifferentiableAt ℝ (fun y => fderiv ℝ T y v) x)
    (hI : Q x = 1) (hS : (fderiv ℝ Q x v).transpose = fderiv ℝ Q x v) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => T z ⬝ᵥ (Q z *ᵥ T z)) y v) x v =
      2 * (T x ⬝ᵥ fderiv ℝ (fun y => fderiv ℝ T y v) x v) +
      2 * (fderiv ℝ T x v ⬝ᵥ fderiv ℝ T x v) +
      4 * (fderiv ℝ T x v ⬝ᵥ (fderiv ℝ Q x v *ᵥ T x)) +
      T x ⬝ᵥ (fderiv ℝ (fun y => fderiv ℝ Q y v) x v *ᵥ T x) := by
  have heq : (fun y => fderiv ℝ (fun z => T z ⬝ᵥ (Q z *ᵥ T z)) y v) =
      fun y => fderiv ℝ T y v ⬝ᵥ (Q y *ᵥ T y) +
        T y ⬝ᵥ (fderiv ℝ Q y v *ᵥ T y + Q y *ᵥ fderiv ℝ T y v) := by
    funext y
    exact fderiv_quadratic_apply (hQ y) (hT y) v
  rw [heq]
  have hQT := differentiableAt_mulVec (hQ x) (hT x)
  have hQvT := differentiableAt_mulVec hQv (hT x)
  have hQTv := differentiableAt_mulVec (hQ x) hTv
  have hSum : DifferentiableAt ℝ
      (fun y => fderiv ℝ Q y v *ᵥ T y + Q y *ᵥ fderiv ℝ T y v) x := hQvT.add hQTv
  rw [fderiv_fun_add (differentiableAt_dotProduct hTv hQT)
    (differentiableAt_dotProduct (hT x) hSum)]
  simp only [_root_.add_apply]
  rw [fderiv_dotProduct_apply hTv hQT v,
    fderiv_dotProduct_apply (hT x) hSum v,
    fderiv_fun_add hQvT hQTv]
  simp only [_root_.add_apply]
  rw [fderiv_mulVec_apply (hQ x) (hT x) v,
    fderiv_mulVec_apply hQv (hT x) v, fderiv_mulVec_apply (hQ x) hTv v, hI]
  simp only [Matrix.one_mulVec, dotProduct_add]
  have hSym : T x ⬝ᵥ (fderiv ℝ Q x v *ᵥ fderiv ℝ T x v) =
      fderiv ℝ T x v ⬝ᵥ (fderiv ℝ Q x v *ᵥ T x) := by
    rw [← hS, Matrix.dotProduct_transpose_mulVec, hS]
  rw [hSym, dotProduct_comm (fderiv ℝ (fun y => fderiv ℝ T y v) x v) (T x)]
  ring

end KLS.TensorEnergy
end
#print axioms KLS.TensorEnergy.fderiv_fderiv_quadratic_at_identity

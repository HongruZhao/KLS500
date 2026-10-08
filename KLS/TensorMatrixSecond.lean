import KLS.TensorSlotLinear
import KLS.MatrixInverseSecond

/-! Actual second tensor-product derivatives at an identity family. -/
open Matrix
open scoped BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS.TensorEnergy
open KLS.MatrixCalculus
variable {n r : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fderiv_tensorMatrixFamily_update_identity
    {A : E → Fin r → Matrix (Fin n) (Fin n) ℝ} {B : E → Matrix (Fin n) (Fin n) ℝ}
    {x : E} (hA : ∀ j, DifferentiableAt ℝ (fun y => A y j) x)
    (hB : DifferentiableAt ℝ B x) (hI : ∀ j, A x j = 1) (s : Fin r) (v : E) :
    fderiv ℝ (fun y => tensorMatrixFamily (Function.update (A y) s (B y))) x v =
      tensorSlot s (fderiv ℝ B x v) +
      ∑ t ∈ Finset.univ.erase s, tensorSlot s (B x) * tensorSlot t (fderiv ℝ (fun y => A y t) x v) := by
  have hC : ∀ j, DifferentiableAt ℝ (fun y => Function.update (A y) s (B y) j) x := by
    intro j
    by_cases hj : j=s
    · subst j
      simpa only [Function.update_self] using hB
    · simpa only [Function.update_of_ne hj] using hA j
  rw [fderiv_tensorMatrixFamily_apply hC v]
  have heq : A x = fun _ => 1 := funext hI
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s)]
  congr 1
  · simp only [heq, Function.update_self, Function.update_idem, ← tensorSlot_eq_update]
  · apply Finset.sum_congr rfl
    intro t ht
    have hts : t ≠ s := Finset.ne_of_mem_erase ht
    simp only [Function.update_of_ne hts, heq]
    exact tensorMatrixFamily_two_updates hts.symm _ _

/-- A second derivative is the sum of each second factor derivative and
all ordered pairs of distinct first factor derivatives. -/
theorem fderiv_fderiv_tensorMatrixFamily_identity
    {A : E → Fin r → Matrix (Fin n) (Fin n) ℝ} {x : E}
    (hA : ∀ j, Differentiable ℝ (fun y => A y j)) (v w : E)
    (hAv : ∀ j, DifferentiableAt ℝ (fun y => fderiv ℝ (fun z => A z j) y v) x)
    (hI : ∀ j, A x j = 1) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => tensorMatrixFamily (A z)) y v) x w =
      ∑ s, (tensorSlot s (fderiv ℝ (fun y => fderiv ℝ (fun z => A z s) y v) x w) +
        ∑ t ∈ Finset.univ.erase s,
          tensorSlot s (fderiv ℝ (fun y => A y s) x v) *
          tensorSlot t (fderiv ℝ (fun y => A y t) x w)) := by
  have hEq : (fun y => fderiv ℝ (fun z => tensorMatrixFamily (A z)) y v) =
      fun y => ∑ s, tensorMatrixFamily (Function.update (A y) s (fderiv ℝ (fun z => A z s) y v)) := by
    funext y
    exact fderiv_tensorMatrixFamily_apply (fun j => hA j y) v
  rw [hEq]
  have hEach : ∀ s : Fin r,
      DifferentiableAt ℝ (fun y => tensorMatrixFamily (Function.update (A y) s (fderiv ℝ (fun z => A z s) y v))) x := by
    intro s
    apply differentiableAt_tensorMatrixFamily
    intro j
    by_cases hjs : j=s
    · subst j
      simpa only [Function.update_self] using hAv s
    · simpa only [Function.update_of_ne hjs] using hA j x
  rw [fderiv_fun_sum (u := Finset.univ) (fun s _ => hEach s)]
  simp only [_root_.sum_apply]
  apply Finset.sum_congr rfl
  intro s _
  exact fderiv_tensorMatrixFamily_update_identity (fun j => hA j x) (hAv s) hI s w

end KLS.TensorEnergy
end
#print axioms KLS.TensorEnergy.fderiv_fderiv_tensorMatrixFamily_identity

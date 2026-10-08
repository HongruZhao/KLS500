import KLS.TensorMatrixFamily

/-! Genuine first differentials of finite tensor matrix products. -/
open Matrix
open scoped BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS.TensorEnergy
open KLS.MatrixCalculus
variable {n r : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem tensorMatrixFamily_update_apply (A : Fin r → Matrix (Fin n) (Fin n) ℝ)
    (s : Fin r) (H : Matrix (Fin n) (Fin n) ℝ) (a b : Fin r → Fin n) :
    tensorMatrixFamily (Function.update A s H) a b =
      (∏ j ∈ Finset.univ.erase s, A j (a j) (b j)) * H (a s) (b s) := by
  unfold tensorMatrixFamily
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ s)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

theorem differentiableAt_tensorMatrixFamily {A : E → Fin r → Matrix (Fin n) (Fin n) ℝ}
    {x : E} (hA : ∀ s, DifferentiableAt ℝ (fun y => A y s) x) :
    DifferentiableAt ℝ (fun y => tensorMatrixFamily (A y)) x := by
  apply differentiableAt_pi.mpr
  intro a
  apply differentiableAt_pi.mpr
  intro b
  change DifferentiableAt ℝ (fun y => ∏ s, A y s (a s) (b s)) x
  exact (HasFDerivAt.finsetProd (u := Finset.univ) fun s _ =>
    (differentiableAt_matrix_entry (hA s) (a s) (b s)).hasFDerivAt).differentiableAt

theorem fderiv_tensorMatrixFamily_apply {A : E → Fin r → Matrix (Fin n) (Fin n) ℝ}
    {x : E} (hA : ∀ s, DifferentiableAt ℝ (fun y => A y s) x) (v : E) :
    fderiv ℝ (fun y => tensorMatrixFamily (A y)) x v =
      ∑ s, tensorMatrixFamily (Function.update (A x) s (fderiv ℝ (fun y => A y s) x v)) := by
  ext a b
  rw [← fderiv_matrix_entry (differentiableAt_tensorMatrixFamily hA)]
  change fderiv ℝ (fun y => ∏ s, A y s (a s) (b s)) x v = _
  have hh := fderiv_finsetProd (u := Finset.univ)
    (g := fun s y => A y s (a s) (b s))
    (fun s _ => differentiableAt_matrix_entry (hA s) (a s) (b s))
  have hv := congrArg (fun L : E →L[ℝ] ℝ => L v) hh
  simp only [_root_.sum_apply, _root_.smul_apply,
    smul_eq_mul, fderiv_matrix_entry (hA _)] at hv ⊢
  rw [hv]
  rw [Matrix.sum_apply]
  exact Finset.sum_congr rfl fun s _ => (tensorMatrixFamily_update_apply _ s _ a b).symm

/-- At an identity family, the first differential is the sum of the actual
one-slot actions. -/
theorem fderiv_tensorMatrixFamily_identity {A : E → Fin r → Matrix (Fin n) (Fin n) ℝ}
    {x : E} (hA : ∀ s, DifferentiableAt ℝ (fun y => A y s) x)
    (hI : ∀ s, A x s = 1) (v : E) :
    fderiv ℝ (fun y => tensorMatrixFamily (A y)) x v =
      ∑ s, tensorSlot s (fderiv ℝ (fun y => A y s) x v) := by
  rw [fderiv_tensorMatrixFamily_apply hA v]
  apply Finset.sum_congr rfl
  intro s _
  unfold tensorSlot
  congr 1
  funext j
  by_cases hjs : j=s
  · subst j
    simp
  · simp [Function.update_of_ne hjs, hjs, hI]

end KLS.TensorEnergy
end
#print axioms KLS.TensorEnergy.fderiv_tensorMatrixFamily_apply
#print axioms KLS.TensorEnergy.fderiv_tensorMatrixFamily_identity

import OptSymmetricTensorAction
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Matrix.Hermitian

/-! The actual permutation-fixed coordinate subspace is invariant under slot sums. -/
open Matrix Set
open scoped BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS.TensorEnergy
variable {n r : ℕ}

def coordinateReindexEquiv (σ : Equiv.Perm (Fin r)) :
    (Fin r → Fin n) ≃ (Fin r → Fin n) where
  toFun a := a ∘ σ
  invFun a := a ∘ σ.symm
  left_inv a := by funext i; simp
  right_inv a := by funext i; simp

def symmetricTensorSubspace (n r : ℕ) : Submodule ℝ (EuclideanSpace ℝ (Fin r → Fin n)) where
  carrier := {T | ∀ (σ : Equiv.Perm (Fin r)) a, T (a ∘ σ) = T a}
  zero_mem' := by simp
  add_mem' := by intro T U hT hU σ a; simp only [PiLp.add_apply]; rw [hT σ a, hU σ a]
  smul_mem' := by intro c T hT σ a; simp only [PiLp.smul_apply]; rw [hT σ a]

theorem tensorMatrix_reindex (H : Matrix (Fin n) (Fin n) ℝ)
    (σ : Equiv.Perm (Fin r)) (a b : Fin r → Fin n) :
    tensorMatrix H (a ∘ σ) (b ∘ σ) = tensorMatrix H a b := by
  exact Equiv.prod_comp σ (fun s => H (a s) (b s))

theorem fderiv_tensorMatrix_identity (H : Matrix (Fin n) (Fin n) ℝ) :
    fderiv ℝ (tensorMatrix (r := r)) 1 H = tensorSlotSum H := by
  have hh := fderiv_tensorMatrixFamily_identity (r := r)
    (A := fun M : Matrix (Fin n) (Fin n) ℝ => fun _ : Fin r => M)
    (x := 1) (fun _ => differentiableAt_id) (fun _ => rfl) H
  change fderiv ℝ (fun M : Matrix (Fin n) (Fin n) ℝ => tensorMatrixFamily (fun _ : Fin r => M)) 1 H = _
  simpa only [fderiv_fun_id, ContinuousLinearMap.id_apply, tensorSlotSum] using hh

theorem tensorSlotSum_reindex (H : Matrix (Fin n) (Fin n) ℝ)
    (σ : Equiv.Perm (Fin r)) (a b : Fin r → Fin n) :
    tensorSlotSum H (a ∘ σ) (b ∘ σ) = tensorSlotSum H a b := by
  have hd : DifferentiableAt ℝ (tensorMatrix (n := n) (r := r)) (1 : Matrix (Fin n) (Fin n) ℝ) :=
    differentiableAt_tensorMatrixFamily (fun _ => differentiableAt_id)
  have he : (fun M : Matrix (Fin n) (Fin n) ℝ => tensorMatrix M (a ∘ σ) (b ∘ σ)) =
      (fun M => tensorMatrix M a b) := by
    funext M
    exact tensorMatrix_reindex M σ a b
  have h := congrArg (fun f : Matrix (Fin n) (Fin n) ℝ → ℝ => fderiv ℝ f 1 H) he
  simpa only [KLS.MatrixCalculus.fderiv_matrix_entry hd, fderiv_tensorMatrix_identity] using h

theorem tensorSlotSum_preserves_symmetry (H : Matrix (Fin n) (Fin n) ℝ)
    (T : (Fin r → Fin n) → ℝ)
    (hT : ∀ (σ : Equiv.Perm (Fin r)) a, T (a ∘ σ) = T a) :
    ∀ (σ : Equiv.Perm (Fin r)) a,
      (tensorSlotSum H *ᵥ T) (a ∘ σ) = (tensorSlotSum H *ᵥ T) a := by
  intro σ a
  change (∑ b, tensorSlotSum H (a ∘ σ) b * T b) = ∑ b, tensorSlotSum H a b * T b
  calc
    _ = ∑ b, tensorSlotSum H (a ∘ σ) (b ∘ σ) * T (b ∘ σ) :=
      ((coordinateReindexEquiv (n := n) σ).sum_comp
        (fun b => tensorSlotSum H (a ∘ σ) b * T b)).symm
    _ = _ := by simp only [tensorSlotSum_reindex, hT]

def symmetricTensorSlot (H : Matrix (Fin n) (Fin n) ℝ) :
    symmetricTensorSubspace n r →ₗ[ℝ] symmetricTensorSubspace n r :=
  (tensorSlotSum H).toEuclideanLin.restrict
    (fun T hT => tensorSlotSum_preserves_symmetry H T hT)

theorem symmetricTensorSlot_apply (H : Matrix (Fin n) (Fin n) ℝ)
    (T : symmetricTensorSubspace n r) (a : Fin r → Fin n) :
    (symmetricTensorSlot H T).val a = (tensorSlotSum H *ᵥ T.val.ofLp) a := rfl

theorem symmetricTensorSlot_isSymmetric (H : Matrix (Fin n) (Fin n) ℝ)
    (hH : H.transpose = H) : (symmetricTensorSlot (r := r) H).IsSymmetric := by
  have hM : (tensorSlotSum (r := r) H).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial,
      tensorSlotSum_transpose, hH]
  have hs := Matrix.isSymmetric_toEuclideanLin_iff.mpr hM
  intro T U
  exact hs T.val U.val

end KLS.TensorEnergy
end

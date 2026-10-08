import OptSymmetricTensorPolynomial

/-! The slot-sum action is the Lie derivative along a linear vector field. -/
open Matrix Set
open scoped BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
noncomputable section
namespace KLS.TensorEnergy
variable {n r : ℕ}

def pureCoordinateTensor (x : Fin n → ℝ) : (Fin r → Fin n) → ℝ :=
  fun a => ∏ s, x (a s)

theorem tensorMatrixFamily_pureCoordinate (A : Fin r → Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) (a : Fin r → Fin n) :
    (tensorMatrixFamily A *ᵥ pureCoordinateTensor x) a = ∏ s, (A s *ᵥ x) (a s) := by
  simp only [Matrix.mulVec, dotProduct, tensorMatrixFamily, pureCoordinateTensor]
  rw [Fintype.prod_sum]
  exact Finset.sum_congr rfl fun b _ => Finset.prod_mul_distrib.symm

theorem tensorSlot_pureCoordinate (s : Fin r) (H : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) (a : Fin r → Fin n) :
    (tensorSlot s H *ᵥ pureCoordinateTensor x) a =
      (∏ j ∈ Finset.univ.erase s, x (a j)) * (H *ᵥ x) (a s) := by
  rw [tensorSlot, tensorMatrixFamily_pureCoordinate]
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ s)]
  rw [ite_eq_left rfl]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [ite_eq_right (Finset.ne_of_mem_erase hj), Matrix.one_mulVec]

theorem tensorPolynomial_slot (T : (Fin r → Fin n) → ℝ) (s : Fin r)
    (H : Matrix (Fin n) (Fin n) ℝ) (x : Space n) :
    tensorPolynomial (tensorSlot s H *ᵥ T) x =
      ∑ a, T a * (∏ j ∈ Finset.univ.erase s, x (a j)) * (H.transpose *ᵥ x.ofLp) (a s) := by
  change (tensorSlot s H *ᵥ T) ⬝ᵥ pureCoordinateTensor x.ofLp = _
  rw [dotProduct_comm, ← Matrix.dotProduct_transpose_mulVec, tensorSlot_transpose]
  simp only [dotProduct, tensorSlot_pureCoordinate]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem tensorPolynomial_slotSum (T : (Fin r → Fin n) → ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (x : Space n) :
    tensorPolynomial (tensorSlotSum H *ᵥ T) x =
      fderiv ℝ (tensorPolynomial T) x (H.transpose.toEuclideanLin x) := by
  rw [tensorSlotSum, Matrix.sum_mulVec, tensorPolynomial_sum, fderiv_tensorPolynomial]
  simp_rw [tensorPolynomial_slot]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  change T a * (∏ j ∈ Finset.univ.erase s, x (a j)) *
      (H.transpose *ᵥ x.ofLp) (a s) =
    T a * ((∏ j ∈ Finset.univ.erase s, x (a j)) *
      (H.transpose *ᵥ x.ofLp) (a s))
  ring


theorem tensorPolynomial_slotSum_square (T : (Fin r → Fin n) → ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.transpose = H) (x : Space n) :
    tensorPolynomial (tensorSlotSum H *ᵥ (tensorSlotSum H *ᵥ T)) x =
      fderiv ℝ (fderiv ℝ (tensorPolynomial T)) x (H.toEuclideanLin x) (H.toEuclideanLin x) +
      fderiv ℝ (tensorPolynomial T) x (H.toEuclideanLin (H.toEuclideanLin x)) := by
  let A : Space n →L[ℝ] Space n := H.toEuclideanLin.toContinuousLinearMap
  have he : tensorPolynomial (tensorSlotSum H *ᵥ T) =
      (fun y => fderiv ℝ (tensorPolynomial T) y (A y)) := by
    funext y
    rw [tensorPolynomial_slotSum, hH]
    rfl
  have hd : DifferentiableAt ℝ (fderiv ℝ (tensorPolynomial T)) x :=
    ((contDiff_tensorPolynomial T).fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable
      (by simp) x
  rw [tensorPolynomial_slotSum, hH, he]
  rw [fderiv_clm_apply hd A.differentiableAt]
  rw [A.fderiv]
  simp only [_root_.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
  change fderiv ℝ (tensorPolynomial T) x (H.toEuclideanLin (H.toEuclideanLin x)) +
    fderiv ℝ (fderiv ℝ (tensorPolynomial T)) x (H.toEuclideanLin x) (H.toEuclideanLin x) = _
  ring

end KLS.TensorEnergy
end

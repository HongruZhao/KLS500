import KLS.AdaptiveMaximalCumulantIto

/-! Actual finite tensor products of matrix actions, in full coordinate arrays. -/
open Matrix
open scoped BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS.TensorEnergy
variable {n r : ℕ}

/-- Full coordinate matrix of the product of one matrix in each tensor slot. -/
def tensorMatrixFamily (A : Fin r → Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin r → Fin n) (Fin r → Fin n) ℝ :=
  fun a b => ∏ s : Fin r, A s (a s) (b s)

def tensorMatrix (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin r → Fin n) (Fin r → Fin n) ℝ := tensorMatrixFamily (fun _ => A)

theorem tensorMatrixFamily_transpose (A : Fin r → Matrix (Fin n) (Fin n) ℝ) :
    tensorMatrixFamily (fun s => (A s).transpose) = (tensorMatrixFamily A).transpose := rfl

theorem tensorMatrixFamily_one :
    tensorMatrixFamily (fun _ : Fin r => (1 : Matrix (Fin n) (Fin n) ℝ)) = 1 := by
  ext a b
  by_cases hab : a = b
  · subst b
    simp [tensorMatrixFamily]
  · have hne : ∃ s, a s ≠ b s := by
      by_contra hh
      push_neg at hh
      exact hab (funext hh)
    obtain ⟨s, hs⟩ := hne
    simp only [tensorMatrixFamily, Matrix.one_apply, hab, ite_false]
    exact Finset.prod_eq_zero (Finset.mem_univ s) (if_neg hs)

theorem tensorMatrixFamily_mul (A B : Fin r → Matrix (Fin n) (Fin n) ℝ) :
    tensorMatrixFamily (fun s => A s * B s) = tensorMatrixFamily A * tensorMatrixFamily B := by
  ext a b
  simp only [tensorMatrixFamily, Matrix.mul_apply]
  rw [Fintype.prod_sum]
  exact Finset.sum_congr rfl fun c _ => Finset.prod_mul_distrib

theorem tensorMatrix_one : tensorMatrix (r := r) (1 : Matrix (Fin n) (Fin n) ℝ) = 1 :=
  tensorMatrixFamily_one

theorem tensorMatrix_mul (A B : Matrix (Fin n) (Fin n) ℝ) :
    tensorMatrix (r := r) (A*B) = tensorMatrix A * tensorMatrix B :=
  tensorMatrixFamily_mul (fun _ => A) (fun _ => B)

theorem tensorMatrix_transpose (A : Matrix (Fin n) (Fin n) ℝ) :
    tensorMatrix (r := r) A.transpose = (tensorMatrix A).transpose := rfl

/-- The operator acting as H in one specified slot and identity in every other slot. -/
def tensorSlot (s : Fin r) (H : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin r → Fin n) (Fin r → Fin n) ℝ :=
  tensorMatrixFamily (fun j => if j=s then H else 1)

theorem tensorSlot_mul (s : Fin r) (H K : Matrix (Fin n) (Fin n) ℝ) :
    tensorSlot s (H*K) = tensorSlot s H * tensorSlot s K := by
  simp only [tensorSlot, ← tensorMatrixFamily_mul]
  congr 1
  funext j
  by_cases hj : j=s <;> simp [hj]

theorem tensorSlot_commute {s t : Fin r} (hst : s ≠ t)
    (H K : Matrix (Fin n) (Fin n) ℝ) :
    tensorSlot s H * tensorSlot t K = tensorSlot t K * tensorSlot s H := by
  simp only [tensorSlot, ← tensorMatrixFamily_mul]
  congr 1
  funext j
  by_cases hjs : j=s
  · subst j
    simp [hst]
  · by_cases hjt : j=t
    · subst j
      simp [hjs]
    · simp [hjs, hjt]

theorem tensorSlot_transpose (s : Fin r) (H : Matrix (Fin n) (Fin n) ℝ) :
    (tensorSlot s H).transpose = tensorSlot s H.transpose := by
  rw [tensorSlot, ← tensorMatrixFamily_transpose]
  congr 1
  funext j
  by_cases hj : j=s <;> simp [hj]

end KLS.TensorEnergy
end
#print axioms KLS.TensorEnergy.tensorMatrixFamily_mul
#print axioms KLS.TensorEnergy.tensorSlot_commute

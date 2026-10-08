import KLS.TensorMatrixDifferential

/-! Linearity and two distinct slots for actual tensor-coordinate matrix actions. -/
open Matrix
open scoped BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS.TensorEnergy
variable {n r : ℕ}

theorem tensorSlot_eq_update (s : Fin r) (H : Matrix (Fin n) (Fin n) ℝ) :
    tensorSlot s H = tensorMatrixFamily (Function.update (fun _ => 1) s H) := by
  unfold tensorSlot
  congr 1
  funext j
  by_cases hj : j=s <;> simp [tensorSlot, hj, Function.update]

theorem tensorSlot_apply (s : Fin r) (H : Matrix (Fin n) (Fin n) ℝ)
    (a b : Fin r → Fin n) :
    tensorSlot s H a b = (∏ j ∈ Finset.univ.erase s, (1 : Matrix (Fin n) (Fin n) ℝ) (a j) (b j)) * H (a s) (b s) := by
  rw [tensorSlot_eq_update, tensorMatrixFamily_update_apply]

theorem tensorSlot_add (s : Fin r) (H K : Matrix (Fin n) (Fin n) ℝ) :
    tensorSlot s (H+K) = tensorSlot s H + tensorSlot s K := by
  ext a b
  simp [tensorSlot_apply, mul_add]

theorem tensorSlot_smul (s : Fin r) (c : ℝ) (H : Matrix (Fin n) (Fin n) ℝ) :
    tensorSlot s (c • H) = c • tensorSlot s H := by
  ext a b
  simp [tensorSlot_apply, mul_left_comm]

theorem tensorSlot_neg (s : Fin r) (H : Matrix (Fin n) (Fin n) ℝ) :
    tensorSlot s (-H) = -tensorSlot s H := by
  ext a b
  simp [tensorSlot_apply]

theorem tensorSlot_zero (s : Fin r) : tensorSlot s (0 : Matrix (Fin n) (Fin n) ℝ) = 0 := by
  ext a b
  simp [tensorSlot_apply]

theorem tensorSlot_one (s : Fin r) : tensorSlot s (1 : Matrix (Fin n) (Fin n) ℝ) = 1 := by
  simp [tensorSlot, tensorMatrixFamily_one]

theorem tensorMatrixFamily_two_updates {s t : Fin r} (hst : s ≠ t)
    (H K : Matrix (Fin n) (Fin n) ℝ) :
    tensorMatrixFamily (Function.update (Function.update (fun _ => 1) s H) t K) =
      tensorSlot s H * tensorSlot t K := by
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

end KLS.TensorEnergy
end
#print axioms KLS.TensorEnergy.tensorMatrixFamily_two_updates

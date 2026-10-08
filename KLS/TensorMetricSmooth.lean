import KLS.TensorMetric
import KLS.TensorInverseDerivatives

/-! Smoothness of the actual tensor inverse metric along nonsingular smooth
matrix fields. -/
open Matrix
open scoped BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS.TensorEnergy
variable {n r : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem contDiff_tensorMatrixFamily {A : E → Fin r → Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ s, ContDiff ℝ (⊤ : ℕ∞) (fun y => A y s)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => tensorMatrixFamily (A y)) := by
  apply contDiff_pi.mpr
  intro a
  apply contDiff_pi.mpr
  intro b
  exact contDiff_prod fun s _ => contDiff_pi.mp (contDiff_pi.mp (hA s) (a s)) (b s)

theorem contDiff_tensorInverse {A : E → Matrix (Fin n) (Fin n) ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hdet : ∀ y, (A y).det ≠ 0) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => tensorMatrix (r := r) (A y)⁻¹) := by
  apply contDiff_tensorMatrixFamily
  intro _
  exact KLS.contDiff_inverse_of_entries
    (fun i j => contDiff_pi.mp (contDiff_pi.mp hA i) j) hdet

theorem contDiff_tensorMetric {A : E → Matrix (Fin n) (Fin n) ℝ}
    {T : E → (Fin r → Fin n) → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hdet : ∀ y, (A y).det ≠ 0)
    (hT : ContDiff ℝ (⊤ : ℕ∞) T) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => tensorMetric (A y) (T y)) := by
  have hQ := contDiff_tensorInverse (r := r) hA hdet
  unfold tensorMetric Matrix.mulVec dotProduct
  apply ContDiff.sum
  intro a _
  apply (contDiff_pi.mp hT a).mul
  apply ContDiff.sum
  intro b _
  exact (contDiff_pi.mp (contDiff_pi.mp hQ a) b).mul (contDiff_pi.mp hT b)

theorem tensorSlotSum_transpose (H : Matrix (Fin n) (Fin n) ℝ) :
    (tensorSlotSum (r := r) H).transpose = tensorSlotSum H.transpose := by
  simp only [tensorSlotSum, Matrix.transpose_sum, tensorSlot_transpose]

theorem dotProduct_matrix_square {ι : Type*} [Fintype ι]
    (M : Matrix ι ι ℝ) (hM : M.transpose = M) (T : ι → ℝ) :
    T ⬝ᵥ ((M*M) *ᵥ T) = (M *ᵥ T) ⬝ᵥ (M *ᵥ T) := by
  rw [← Matrix.mulVec_mulVec, ← hM, Matrix.dotProduct_transpose_mulVec, hM]

end KLS.TensorEnergy
end
#print axioms KLS.TensorEnergy.contDiff_tensorMetric

import KLS.WeakMatrixProduct

open MeasureTheory Set Filter Matrix
open scoped BigOperators ContDiff Topology ENNReal Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

theorem matrix_congruence_entry_bound_raw
    (H B : Matrix (Fin n) (Fin n) ℝ) {C : ℝ}
    (hH : ∀ i j, ‖H i j‖ ≤ C) (i j : Fin n) :
    ‖(B * H * B.transpose) i j‖ ≤ ∑ a, ∑ b, ‖B i b‖ * C * ‖B j a‖ := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro a _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro b _
  simp only [norm_mul]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hH b a) (norm_nonneg _)) (norm_nonneg _)

theorem memLp_top_matrixCongruence_raw
    {H : Space n → Matrix (Fin n) (Fin n) ℝ} {μ : Measure (Space n)}
    (hH : ∀ i j, MemLp (fun x => H x i j) ∞ μ)
    (B : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    MemLp (fun x => (B * H x * B.transpose) i j) ∞ μ := by
  have hB (a b : Fin n) : MemLp (fun _ : Space n => B a b) ∞ μ := memLp_top_const _
  exact memLp_top_matrixMul (memLp_top_matrixMul hB hH) (fun a b => hB b a) i j

theorem memLp_two_matrixCongruence_raw
    {T : Space n → Matrix (Fin n) (Fin n) ℝ} {μ : Measure (Space n)}
    (hT : ∀ i j, MemLp (fun x => T x i j) 2 μ)
    (B : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    MemLp (fun x => (B * T x * B.transpose) i j) 2 μ := by
  have hB (a b : Fin n) : MemLp (fun _ : Space n => B a b) ∞ μ := memLp_top_const _
  exact memLp_two_matrixMul_right (memLp_two_matrixMul_left hB hT) (fun a b => hB b a) i j

/-- Constant congruence preserves the exact raw weak derivative and its local
L2 bounds. Neither the source nor the constant matrix must be symmetric. -/
theorem hasLocalWeakCoordinateDerivative_matrixCongruence_raw
    {H T : Space n → Matrix (Fin n) (Fin n) ℝ} {k : Fin n}
    (hT : ∀ i j, HasLocalWeakCoordinateDerivative (fun x => H x i j) (fun x => T x i j) k)
    (hH : ∀ i j K, IsCompact K → MemLp (fun x => H x i j) ∞ (volume.restrict K))
    (hTloc : ∀ i j K, IsCompact K → MemLp (fun x => T x i j) 2 (volume.restrict K))
    (B : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    HasLocalWeakCoordinateDerivative (fun x => (B * H x * B.transpose) i j)
      (fun x => (B * T x * B.transpose) i j) k := by
  have hB (a b : Fin n) (K : Set (Space n)) (_ : IsCompact K) :
      MemLp (fun _ : Space n => B a b) ∞ (volume.restrict K) := memLp_top_const _
  have hzero (a b : Fin n) (K : Set (Space n)) (_ : IsCompact K) :
      MemLp (fun _ : Space n => (0 : Matrix (Fin n) (Fin n) ℝ) a b) 2
        (volume.restrict K) := by simp
  have hDB (a b : Fin n) : HasLocalWeakCoordinateDerivative
      (fun _ : Space n => B a b) (fun _ => (0 : Matrix (Fin n) (Fin n) ℝ) a b) k :=
    hasLocalWeakCoordinateDerivative_const (B a b) k
  have hBH (a b : Fin n) (K : Set (Space n)) (hK : IsCompact K) :
      MemLp (fun x => (B * H x) a b) ∞ (volume.restrict K) :=
    memLp_top_matrixMul (fun c d => hB c d K hK) (fun c d => hH c d K hK) a b
  have hDBH (a b : Fin n) : HasLocalWeakCoordinateDerivative
      (fun x => (B * H x) a b) (fun x => (B * T x) a b) k := by
    simpa only [Matrix.zero_mul, zero_add] using
      hasLocalWeakCoordinateDerivative_matrixMul hDB hT hB hH hzero hTloc a b
  have hDBHloc (a b : Fin n) (K : Set (Space n)) (hK : IsCompact K) :
      MemLp (fun x => (B * T x) a b) 2 (volume.restrict K) :=
    memLp_two_matrixMul_left (fun c d => hB c d K hK) (fun c d => hTloc c d K hK) a b
  have hDC (a b : Fin n) : HasLocalWeakCoordinateDerivative
      (fun _ : Space n => B.transpose a b) (fun _ => (0 : Matrix (Fin n) (Fin n) ℝ) a b) k :=
    hasLocalWeakCoordinateDerivative_const (B.transpose a b) k
  simpa only [Matrix.mul_zero, add_zero] using
    hasLocalWeakCoordinateDerivative_matrixMul hDBH hDC hBH (fun a b => hB b a) hDBHloc hzero i j

end KLS
end

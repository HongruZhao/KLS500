import KLS.RawHessianTraceTerms
import KLS.WeakMomentThirdTensor

open MeasureTheory Matrix
open scoped ENNReal
noncomputable section
namespace KLS
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {n : ℕ}

/-- Entrywise Holder bounds pass through actual finite matrix multiplication. -/
theorem memLp_matrix_mul_entries
    {A B : α → Matrix (Fin n) (Fin n) ℝ} {p q r : ℝ≥0∞}
    [ENNReal.HolderTriple p q r]
    (hA : ∀ i j, MemLp (fun x => A x i j) p μ)
    (hB : ∀ i j, MemLp (fun x => B x i j) q μ) (i j : Fin n) :
    MemLp (fun x => (A x * B x) i j) r μ := by
  simp only [Matrix.mul_apply]
  exact memLp_finsetSum _ (fun k _ => (hA i k).mul (hB k j))

/-- Finite diagonal summation preserves the scalar Lp class. -/
theorem memLp_matrix_trace_entries
    {A : α → Matrix (Fin n) (Fin n) ℝ} {p : ℝ≥0∞}
    (hA : ∀ i j, MemLp (fun x => A x i j) p μ) :
    MemLp (fun x => (A x).trace) p μ := by
  exact memLp_finsetSum _ (fun i _ => hA i i)

/-- Constant matrix entries are essentially bounded for every measure. -/
theorem memLp_constant_matrix_entries (B : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    MemLp (fun _ : α => B i j) ∞ μ :=
  memLp_top_of_bound aestronglyMeasurable_const ‖B i j‖ (Filter.Eventually.of_forall fun _ => le_rfl)

end KLS
end

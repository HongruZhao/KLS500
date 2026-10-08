import KLS.MatrixEntryLpProducts

open MeasureTheory Matrix
open scoped ENNReal
noncomputable section
namespace KLS
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {n : ℕ}

/-- Actual bounded inverse coefficients and L2 tensor entries give an L1
 trace-gradient term by finite Holder products. -/
theorem memLp_rawHessianTraceGradientTerm
    {H : α → Matrix (Fin n) (Fin n) ℝ}
    {T : α → Fin n → Matrix (Fin n) (Fin n) ℝ}
    (hJ : ∀ i j, MemLp (fun x => (H x)⁻¹ i j) ∞ μ)
    (hT : ∀ k i j, MemLp (fun x => T x k i j) 2 μ)
    (B : Matrix (Fin n) (Fin n) ℝ) :
    MemLp (fun x => rawHessianTraceGradientTerm (H x) B (T x)) 1 μ := by
  have hB := memLp_constant_matrix_entries (μ := μ) B
  have hBT (k : Fin n) := memLp_matrix_mul_entries (r := 2) hB (hT k)
  have hBTB (k : Fin n) := memLp_matrix_mul_entries (r := 2) (hBT k) hB
  have hQ (i j : Fin n) := memLp_matrix_trace_entries (memLp_matrix_mul_entries (r := 1) (hBTB i) (hT j))
  exact memLp_finsetSum _ (fun i _ => memLp_finsetSum _ (fun j _ => (hJ i j).mul (hQ i j)))

/-- The quadratic raw third-tensor contraction is L1 when actual Hessian and
 inverse entries are bounded and tensor entries are L2. -/
theorem memLp_rawHessianTraceThirdTerm
    {H : α → Matrix (Fin n) (Fin n) ℝ}
    {T : α → Fin n → Matrix (Fin n) (Fin n) ℝ}
    (hH : ∀ i j, MemLp (fun x => H x i j) ∞ μ)
    (hJ : ∀ i j, MemLp (fun x => (H x)⁻¹ i j) ∞ μ)
    (hT : ∀ k i j, MemLp (fun x => T x k i j) 2 μ)
    (B : Matrix (Fin n) (Fin n) ℝ) :
    MemLp (fun x => rawHessianTraceThirdTerm (H x) B (T x)) 1 μ := by
  have hB := memLp_constant_matrix_entries (μ := μ) B
  have hBHB := memLp_matrix_mul_entries (r := ∞) (memLp_matrix_mul_entries (r := ∞) hB hH) hB
  have hJT (k : Fin n) := memLp_matrix_mul_entries (r := 2) hJ (hT k)
  have hJTJ (k : Fin n) := memLp_matrix_mul_entries (r := 2) (hJT k) hJ
  have hQ (i j : Fin n) : MemLp (fun x => matrixTraceGram (H x)⁻¹ (T x) i j) 1 μ :=
    memLp_matrix_trace_entries (memLp_matrix_mul_entries (hJTJ i) (hT j))
  exact memLp_matrix_trace_entries (memLp_matrix_mul_entries hBHB hQ)

/-- The raw target-curvature term is essentially bounded when each of its
 actual matrix factors is essentially bounded. -/
theorem memLp_rawHessianTraceTargetTerm_top
    {H M : α → Matrix (Fin n) (Fin n) ℝ}
    (hH : ∀ i j, MemLp (fun x => H x i j) ∞ μ)
    (hM : ∀ i j, MemLp (fun x => M x i j) ∞ μ)
    (B : Matrix (Fin n) (Fin n) ℝ) :
    MemLp (fun x => rawHessianTraceTargetTerm (H x) (M x) B) ∞ μ := by
  have hB := memLp_constant_matrix_entries (μ := μ) B
  have hBHB := memLp_matrix_mul_entries (r := ∞) (memLp_matrix_mul_entries (r := ∞) hB hH) hB
  have hHMH := memLp_matrix_mul_entries (r := ∞) (memLp_matrix_mul_entries (r := ∞) hH hM) hH
  exact memLp_matrix_trace_entries (memLp_matrix_mul_entries hBHB hHMH)

end KLS
end

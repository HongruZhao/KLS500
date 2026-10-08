import KLS.WeakMatrixProduct
import KLS.RawHessianTraceTerms

open MeasureTheory Set Filter Matrix
open scoped BigOperators ContDiff Topology ENNReal Matrix.Norms.Elementwise

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

theorem hasLocalWeakCoordinateDerivative_matrixTrace
    {H T : Space n → Matrix (Fin n) (Fin n) ℝ} {k : Fin n}
    (hT : ∀ i j, HasLocalWeakCoordinateDerivative (fun x => H x i j) (fun x => T x i j) k)
    (hH : ∀ i j K, IsCompact K → MemLp (fun x => H x i j) ∞ (volume.restrict K))
    (hTloc : ∀ i j K, IsCompact K → MemLp (fun x => T x i j) 2 (volume.restrict K)) :
    HasLocalWeakCoordinateDerivative (fun x => (H x).trace) (fun x => (T x).trace) k := by
  have hs := hasLocalWeakCoordinateDerivative_finset_sum Finset.univ
    (fun i _ => hT i i)
    (fun i _ => locallyIntegrable_of_memLp_two_on_compacts
      (memLp_two_on_compacts_of_top (hH i i)))
    (fun i _ => locallyIntegrable_of_memLp_two_on_compacts (hTloc i i))
  simpa only [Matrix.trace, Matrix.diag_apply] using hs

theorem rawHessianTraceSquare_memLp_top
    {H : Space n → Matrix (Fin n) (Fin n) ℝ} {μ : Measure (Space n)}
    (hH : ∀ i j, MemLp (fun x => H x i j) ∞ μ)
    (B : Matrix (Fin n) (Fin n) ℝ) :
    MemLp (fun x => rawHessianTraceSquare (H x) B) ∞ μ := by
  have hB (i j : Fin n) : MemLp (fun _ : Space n => B i j) ∞ μ := memLp_top_const _
  have hBH := memLp_top_matrixMul hB hH
  have hBHB := memLp_top_matrixMul hBH hB
  have hQ := memLp_top_matrixMul hBHB hH
  unfold rawHessianTraceSquare Matrix.trace
  exact memLp_finsetSum _ (fun i _ => hQ i i)

theorem rawHessianTraceSquare_derivative_memLp_two
    {H T : Space n → Matrix (Fin n) (Fin n) ℝ} {μ : Measure (Space n)}
    (hH : ∀ i j, MemLp (fun x => H x i j) ∞ μ)
    (hT : ∀ i j, MemLp (fun x => T x i j) 2 μ)
    (B : Matrix (Fin n) (Fin n) ℝ) :
    MemLp (fun x => 2 * (B * H x * B * T x).trace) 2 μ := by
  have hB (i j : Fin n) : MemLp (fun _ : Space n => B i j) ∞ μ := memLp_top_const _
  have hBH := memLp_top_matrixMul hB hH
  have hBHB := memLp_top_matrixMul hBH hB
  have hQ := memLp_two_matrixMul_left hBHB hT
  have hs : MemLp (fun x => (B * H x * B * T x).trace) 2 μ := by
    unfold Matrix.trace
    exact memLp_finsetSum _ (fun i _ => hQ i i)
  exact hs.const_mul 2

/-- The actual raw local weak derivative of the trace square, with its
noncommuting matrix order retained. No classical derivative is assumed. -/
theorem hasLocalWeakCoordinateDerivative_rawHessianTraceSquare
    {H T : Space n → Matrix (Fin n) (Fin n) ℝ} {k : Fin n}
    (hT : ∀ i j, HasLocalWeakCoordinateDerivative (fun x => H x i j) (fun x => T x i j) k)
    (hH : ∀ i j K, IsCompact K → MemLp (fun x => H x i j) ∞ (volume.restrict K))
    (hTloc : ∀ i j K, IsCompact K → MemLp (fun x => T x i j) 2 (volume.restrict K))
    (B : Matrix (Fin n) (Fin n) ℝ) :
    HasLocalWeakCoordinateDerivative (fun x => rawHessianTraceSquare (H x) B)
      (fun x => 2 * (B * H x * B * T x).trace) k := by
  have hB (i j : Fin n) (K : Set (Space n)) (_ : IsCompact K) :
      MemLp (fun _ : Space n => B i j) ∞ (volume.restrict K) := memLp_top_const _
  have hzero (i j : Fin n) (K : Set (Space n)) (_ : IsCompact K) :
      MemLp (fun _ : Space n => (0 : Matrix (Fin n) (Fin n) ℝ) i j) 2
        (volume.restrict K) := by
    simp
  have hDB (i j : Fin n) : HasLocalWeakCoordinateDerivative
      (fun _ : Space n => B i j) (fun _ => (0 : Matrix (Fin n) (Fin n) ℝ) i j) k :=
    hasLocalWeakCoordinateDerivative_const (B i j) k
  have hBH (i j : Fin n) (K : Set (Space n)) (hK : IsCompact K) :
      MemLp (fun x => (B * H x) i j) ∞ (volume.restrict K) :=
    memLp_top_matrixMul (fun a b => hB a b K hK) (fun a b => hH a b K hK) i j
  have hDBH (i j : Fin n) : HasLocalWeakCoordinateDerivative
      (fun x => (B * H x) i j) (fun x => (B * T x) i j) k := by
    simpa only [Matrix.zero_mul, zero_add] using
      hasLocalWeakCoordinateDerivative_matrixMul hDB hT hB hH hzero hTloc i j
  have hDBHloc (i j : Fin n) (K : Set (Space n)) (hK : IsCompact K) :
      MemLp (fun x => (B * T x) i j) 2 (volume.restrict K) :=
    memLp_two_matrixMul_left (fun a b => hB a b K hK) (fun a b => hTloc a b K hK) i j
  have hBHB (i j : Fin n) (K : Set (Space n)) (hK : IsCompact K) :
      MemLp (fun x => (B * H x * B) i j) ∞ (volume.restrict K) :=
    memLp_top_matrixMul (fun a b => hBH a b K hK) (fun a b => hB a b K hK) i j
  have hDBHB (i j : Fin n) : HasLocalWeakCoordinateDerivative
      (fun x => (B * H x * B) i j) (fun x => (B * T x * B) i j) k := by
    simpa only [Matrix.mul_zero, add_zero] using
      hasLocalWeakCoordinateDerivative_matrixMul hDBH hDB hBH hB hDBHloc hzero i j
  have hDBHBloc (i j : Fin n) (K : Set (Space n)) (hK : IsCompact K) :
      MemLp (fun x => (B * T x * B) i j) 2 (volume.restrict K) :=
    memLp_two_matrixMul_right (fun a b => hDBHloc a b K hK) (fun a b => hB a b K hK) i j
  have hQ (i j : Fin n) (K : Set (Space n)) (hK : IsCompact K) :
      MemLp (fun x => (B * H x * B * H x) i j) ∞ (volume.restrict K) :=
    memLp_top_matrixMul (fun a b => hBHB a b K hK) (fun a b => hH a b K hK) i j
  have hDQ (i j : Fin n) : HasLocalWeakCoordinateDerivative
      (fun x => (B * H x * B * H x) i j)
      (fun x => (B * T x * B * H x + B * H x * B * T x) i j) k :=
    hasLocalWeakCoordinateDerivative_matrixMul hDBHB hT hBHB hH hDBHBloc hTloc i j
  have hDQloc (i j : Fin n) (K : Set (Space n)) (hK : IsCompact K) :
      MemLp (fun x => (B * T x * B * H x + B * H x * B * T x) i j) 2
        (volume.restrict K) := by
    exact (memLp_two_matrixMul_right (fun a b => hDBHBloc a b K hK)
      (fun a b => hH a b K hK) i j).add
      (memLp_two_matrixMul_left (fun a b => hBHB a b K hK)
        (fun a b => hTloc a b K hK) i j)
  have ht := hasLocalWeakCoordinateDerivative_matrixTrace hDQ hQ hDQloc
  have he : (fun x => (B * T x * B * H x + B * H x * B * T x).trace) =
      fun x => 2 * (B * H x * B * T x).trace := by
    funext x
    rw [Matrix.trace_add]
    have hc : (B * T x * B * H x).trace = (B * H x * B * T x).trace := by
      calc
        _ = ((B * T x) * (B * H x)).trace := by rw [Matrix.mul_assoc]
        _ = ((B * H x) * (B * T x)).trace := Matrix.trace_mul_comm _ _
        _ = _ := by simp only [Matrix.mul_assoc]
    rw [hc]
    ring
  rw [he] at ht
  exact ht

end KLS
end

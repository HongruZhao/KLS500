import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! A uniform quadratic determinant remainder near the identity. The estimate
comes from the exact universal determinant polynomial, not from differentiating
an unknown Monge--Ampere solution. Constants may depend on the dimension. -/
open Matrix Set Metric
open scoped Topology Matrix.Norms.Elementwise
noncomputable section
namespace KLS

private abbrev DetVariable (n : ℕ) := Unit ⊕ (Fin n × Fin n)
private abbrev UniversalEntry (n : ℕ) := MvPolynomial (DetVariable n) ℝ

private def universalMatrix (n : ℕ) : Matrix (Fin n) (Fin n) (UniversalEntry n) :=
  fun i j => MvPolynomial.X (Sum.inr (i,j))

private def determinantRemainderPolynomial (n : ℕ) : UniversalEntry n :=
  let H : Matrix (Fin n) (Fin n) (Polynomial (UniversalEntry n)) :=
    (universalMatrix n).map (Polynomial.C : UniversalEntry n → Polynomial (UniversalEntry n))
  let P : Polynomial (UniversalEntry n) := (1 + (Polynomial.X : Polynomial (UniversalEntry n)) • H).det
  P.divX.divX.eval (MvPolynomial.X (Sum.inl ()))

private def determinantRemainder {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) : ℝ :=
  MvPolynomial.eval (Sum.elim (fun _ => t) (fun ij => M ij.1 ij.2))
    (determinantRemainderPolynomial n)

private lemma determinant_eq_one_add_trace_add_quadratic {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    (1 + t • M).det = 1 + M.trace * t + determinantRemainder M t * t ^ 2 := by
  let ev : UniversalEntry n →+* ℝ :=
    MvPolynomial.eval (Sum.elim (fun _ => t) (fun ij => M ij.1 ij.2))
  have hmat : ev.mapMatrix
      (1 + (MvPolynomial.X (Sum.inl ()) : UniversalEntry n) • universalMatrix n) =
      1 + t • M := by
    ext i j
    simp [RingHom.mapMatrix_apply, universalMatrix, Matrix.one_apply, Matrix.add_apply,
      Matrix.smul_apply, ev, smul_eq_mul]
  have htrace : ev (universalMatrix n).trace = M.trace := by
    simp [Matrix.trace, Matrix.diag, universalMatrix, ev]
  have he := congrArg ev (Matrix.det_one_add_smul
    (MvPolynomial.X (Sum.inl ()) : UniversalEntry n) (universalMatrix n))
  rw [ev.map_det, hmat, map_add, map_add, map_one, map_mul, htrace,
    map_mul, map_pow] at he
  simpa only [ev, MvPolynomial.eval_X, Sum.elim_inl,
    determinantRemainder, determinantRemainderPolynomial] using he

private lemma continuous_determinantRemainder {n : ℕ} :
    Continuous (fun p : Matrix (Fin n) (Fin n) ℝ × ℝ => determinantRemainder p.1 p.2) := by
  apply (MvPolynomial.continuous_eval (determinantRemainderPolynomial n)).comp
  apply continuous_pi
  intro i
  cases i with
  | inl i => exact continuous_snd
  | inr ij => exact (continuous_apply ij.2).comp ((continuous_apply ij.1).comp continuous_fst)

/-- Uniform O(t²) control on the elementwise unit ball of matrices. -/
theorem exists_uniform_det_identity_quadratic_bound (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : Matrix (Fin n) (Fin n) ℝ, ‖M‖ ≤ 1 →
      ∀ t : ℝ, |t| ≤ 1 → |(1 + t • M).det - 1 - M.trace * t| ≤ C * t ^ 2 := by
  let K : Set (Matrix (Fin n) (Fin n) ℝ × ℝ) :=
    closedBall 0 1 ×ˢ Icc (-1) 1
  have hK : IsCompact K := (isCompact_closedBall _ _).prod isCompact_Icc
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn continuous_determinantRemainder.continuousOn
  refine ⟨|B| + 1, by positivity, ?_⟩
  intro M hM t ht
  have hm : (M,t) ∈ K := ⟨by simpa only [mem_closedBall, dist_zero_right] using hM, abs_le.mp ht⟩
  have hb : |determinantRemainder M t| ≤ |B| + 1 := by
    have hh := hB (M,t) hm
    simp only [Real.norm_eq_abs] at hh
    exact hh.trans (by linarith [le_abs_self B])
  rw [determinant_eq_one_add_trace_add_quadratic]
  have he : 1 + M.trace * t + determinantRemainder M t * t ^ 2 - 1 - M.trace * t =
      determinantRemainder M t * t ^ 2 := by ring
  rw [he, abs_mul, abs_sq]
  exact mul_le_mul_of_nonneg_right hb (sq_nonneg t)

end KLS
end

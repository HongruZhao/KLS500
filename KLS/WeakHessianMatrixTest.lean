import KLS.WeakMatrixSandwich
import KLS.WeakHessianCompactTest

open MeasureTheory Set Filter Matrix
open scoped BigOperators ContDiff Topology ENNReal NNReal Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- The actual compact matrix test for weak Hessian trace contraction, with
its global bound, local square integrability, and exact raw H1 derivative. -/
theorem actual_hessian_sandwich_compact_H1_test
    {u χ : Space n → ℝ} {G : ℝ≥0} {T : Space n → Fin n → Matrix (Fin n) (Fin n) ℝ}
    (hG : LipschitzWith G (gradient u))
    (hTl : ∀ k i j S, IsCompact S → MemLp (fun x => T x k i j) 2 (volume.restrict S))
    (hTw : ∀ k i j, HasLocalWeakCoordinateDerivative
      (fun x => coordinateHessian u x i j) (fun x => T x k i j) k)
    (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ)
    (B : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    HasCompactSupport (fun x => χ x * (B * coordinateHessian u x * B) i j) ∧
    (∃ C : ℝ, ∀ x, ‖χ x * (B * coordinateHessian u x * B) i j‖ ≤ C) ∧
    (∀ S, IsCompact S → MemLp (fun x => χ x * (B * coordinateHessian u x * B) i j)
      2 (volume.restrict S)) ∧
    (∀ k S, IsCompact S → MemLp
      (fun x => coordinateDerivative χ k x * (B * coordinateHessian u x * B) i j +
        χ x * (B * T x k * B) i j) 2 (volume.restrict S)) ∧
    ∀ k, HasLocalWeakCoordinateDerivative
      (fun x => χ x * (B * coordinateHessian u x * B) i j)
      (fun x => coordinateDerivative χ k x * (B * coordinateHessian u x * B) i j +
        χ x * (B * T x k * B) i j) k := by
  have hH (a b : Fin n) (S : Set (Space n)) (hS : IsCompact S) :
      MemLp (fun x => coordinateHessian u x a b) ∞ (volume.restrict S) :=
    memLp_top_actual_hessian_of_locallyLipschitz_gradient hG.locallyLipschitz a b hS
  have hQ (S : Set (Space n)) (hS : IsCompact S) :
      MemLp (fun x => (B * coordinateHessian u x * B) i j) ∞ (volume.restrict S) :=
    memLp_top_matrixSandwich (fun a b => hH a b S hS) B i j
  have hQ2 := memLp_two_on_compacts_of_top hQ
  have hDQ (k : Fin n) (S : Set (Space n)) (hS : IsCompact S) :
      MemLp (fun x => (B * T x k * B) i j) 2 (volume.restrict S) :=
    memLp_two_matrixSandwich (fun a b => hTl k a b S hS) B i j
  have hχb (S : Set (Space n)) :=
    (hχ.continuous.memLp_top_of_hasCompactSupport hc volume).restrict S
  have hdχ (k : Fin n) := (contDiff_coordinateDerivative hχ (m := 0) (by norm_num) k).continuous
  have hdχb (k : Fin n) (S : Set (Space n)) :=
    ((hdχ k).memLp_top_of_hasCompactSupport (hasCompactSupport_coordinateDerivative hc k) volume).restrict S
  refine ⟨hc.mul_right, ?_, fun S hS => (hχb S).mul (hQ2 S hS), ?_, ?_⟩
  · obtain ⟨C, hC⟩ := hχ.continuous.bounded_above_of_compact_support hc
    refine ⟨C * (∑ a, ∑ b, ‖B i b‖ * (G : ℝ) * ‖B a j‖), fun x => ?_⟩
    rw [norm_mul]
    exact mul_le_mul (hC x)
      (matrix_sandwich_entry_bound (coordinateHessian u x) B
        (actual_hessian_global_entry_bound hG x) i j)
      (norm_nonneg _) (le_trans (norm_nonneg (χ x)) (hC x))
  · intro k S hS
    have ha : MemLp (fun x => coordinateDerivative χ k x * (B * coordinateHessian u x * B) i j)
        2 (volume.restrict S) := (hdχb k S).mul (hQ2 S hS)
    exact ha.add ((hχb S).mul (hDQ k S hS))
  · intro k
    have hw := hasLocalWeakCoordinateDerivative_matrixSandwich (hTw k) hH (hTl k) B i j
    exact (hasLocalWeakCoordinateDerivative_of_contDiff hχ k).mul hw
      (fun S _ => (hχ.continuous.memLp_of_hasCompactSupport hc).restrict S) hQ2
      (fun S _ => ((hdχ k).memLp_of_hasCompactSupport
        (hasCompactSupport_coordinateDerivative hc k)).restrict S) (hDQ k)

end KLS
end

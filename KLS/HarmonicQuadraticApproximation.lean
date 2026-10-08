import KLS.HarmonicCubicTaylor

open MeasureTheory InnerProductSpace Set Filter Metric
open scoped ContDiff Topology BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

/-- A radius chosen from dimension, outer radius, size, and desired quadratic
error; it does not depend on the individual harmonic function. -/
def harmonicApproximationRadius (n : ℕ) (R B η : ℝ) : ℝ :=
  min (R / 8) (η / (harmonicCubicTaylorConstant n R B + 1))

lemma harmonicApproximationRadius_pos {R B η : ℝ} (hR : 0 < R) (hη : 0 < η) :
    0 < harmonicApproximationRadius n R B η := by
  have hC := harmonicCubicTaylorConstant_nonneg n R B
  unfold harmonicApproximationRadius
  positivity

lemma harmonicApproximationRadius_le (R B η : ℝ) :
    harmonicApproximationRadius n R B η ≤ R / 8 := min_le_left _ _

lemma harmonicCubicTaylorConstant_mul_radius_le {R B η : ℝ}
    (hR : 0 < R) (hη : 0 < η) :
    harmonicCubicTaylorConstant n R B * harmonicApproximationRadius n R B η ≤ η := by
  have hC := harmonicCubicTaylorConstant_nonneg n R B
  have hd : 0 < harmonicCubicTaylorConstant n R B + 1 := by linarith
  have hp := harmonicApproximationRadius_pos (n := n) (B := B) hR hη
  have hb : harmonicApproximationRadius n R B η *
      (harmonicCubicTaylorConstant n R B + 1) ≤ η :=
    (le_div_iff₀ hd).mp (min_le_right _ _)
  nlinarith

/-- Uniform-radius quadratic approximation by the genuine harmonic Taylor
polynomial. Its Hessian is symmetric and has zero trace. -/
theorem IsViscosityHarmonicOn.quadratic_approximation
    {U : Set (Space n)} {f : Space n → ℝ} (hf : IsViscosityHarmonicOn U f)
    (hU : IsOpen U) {c : Space n} {R B η : ℝ} (hR : 0 < R) (hη : 0 < η)
    (hball : closedBall c R ⊆ U) (hb : ∀ y ∈ closedBall c R, f y ^ 2 ≤ B) :
    (coordinateHessian f c).IsSymm ∧ (coordinateHessian f c).trace = 0 ∧
      ∀ x ∈ closedBall c (harmonicApproximationRadius n R B η),
        |f x - centeredQuadratic (coordinateHessian f c) c (gradient f c) (f c) x| ≤
          η * ‖x - c‖ ^ 2 := by
  have hc : c ∈ U := hball (mem_closedBall_self hR.le)
  refine ⟨coordinateHessian_isSymm_of_contDiffAt
    (((hf.contDiffOn hU) c hc).contDiffAt (hU.mem_nhds hc) |>.of_le (by simp)), ?_, ?_⟩
  · exact hf.coordinateLaplacian_eq_zero hU hc
  · intro x hx
    have hxr : ‖x-c‖ ≤ harmonicApproximationRadius n R B η := hx
    have hxR := closedBall_subset_closedBall (harmonicApproximationRadius_le R B η) hx
    have h := hf.abs_sub_quadratic_taylor_le hU hR hball hb hxR
    have hcoef : harmonicCubicTaylorConstant n R B * ‖x-c‖ ≤ η :=
      (mul_le_mul_of_nonneg_left hxr (harmonicCubicTaylorConstant_nonneg n R B)).trans
        (harmonicCubicTaylorConstant_mul_radius_le hR hη)
    calc
      _ ≤ harmonicCubicTaylorConstant n R B * ‖x-c‖ ^ 3 := h
      _ = (harmonicCubicTaylorConstant n R B * ‖x-c‖) * ‖x-c‖ ^ 2 := by ring
      _ ≤ η * ‖x-c‖ ^ 2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)


/-- The coefficients of the same Taylor polynomial are uniformly controlled
by the size on the outer ball. -/
theorem IsViscosityHarmonicOn.taylor_coefficients_sq_le
    {U : Set (Space n)} {f : Space n → ℝ} (hf : IsViscosityHarmonicOn U f)
    (hU : IsOpen U) {c : Space n} {R B : ℝ} (hR : 0 < R)
    (hball : closedBall c R ⊆ U) (hb : ∀ y ∈ closedBall c R, f y ^ 2 ≤ B) :
    f c ^ 2 ≤ B ∧
      (∀ i, (gradient f c i) ^ 2 ≤ (120 + 8 * n) * B / R ^ 2) ∧
      (∀ i j, (coordinateHessian f c i j) ^ 2 ≤ 4 * (120 + 8 * n) ^ 2 * B / R ^ 4) := by
  refine ⟨hb c (mem_closedBall_self hR.le), ?_, ?_⟩
  · intro i
    rw [← coordinateDerivative_eq_gradient]
    exact hf.coordinateDerivative_sq_le hU hR hball hb i (mem_closedBall_self (by positivity))
  · intro i j
    have h := hf.harmonicCoordinateWord_sq_le hU hR hball hb [i,j]
      (x := c) (mem_closedBall_self (by positivity))
    change harmonicCoordinateWord [i,j] f c ^ 2 ≤ _
    simpa only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
      harmonicDerivativeFactor_two, div_mul_eq_mul_div] using h

end KLS
end

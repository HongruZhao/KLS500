import KLS.CubicCoordinateTaylor

open MeasureTheory InnerProductSpace Set Filter Metric
open scoped ContDiff Topology BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

/-- A concrete dimension-, radius-, and size-dependent harmonic Taylor constant. -/
def harmonicCubicTaylorConstant (n : ℕ) (R B : ℝ) : ℝ :=
  (n : ℝ) ^ 3 * Real.sqrt (64 * (120 + 8 * n) ^ 3 * B / R ^ 6)

lemma harmonicCubicTaylorConstant_nonneg (n : ℕ) (R B : ℝ) :
    0 ≤ harmonicCubicTaylorConstant n R B := by
  unfold harmonicCubicTaylorConstant
  positivity

/-- Uniform cubic approximation of a harmonic function by its actual second
Taylor polynomial, with all third derivative bounds derived from its size. -/
theorem abs_sub_quadratic_taylor_le_of_harmonicOn {f : Space n → ℝ}
    {U : Set (Space n)} (hU : IsOpen U) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U)
    (hh : ∀ y ∈ U, coordinateLaplacian f y = 0)
    {c x : Space n} {R B : ℝ} (hR : 0 < R) (hball : closedBall c R ⊆ U)
    (hb : ∀ y ∈ closedBall c R, f y ^ 2 ≤ B) (hx : x ∈ closedBall c (R / 8)) :
    |f x - centeredQuadratic (coordinateHessian f c) c (gradient f c) (f c) x| ≤
      harmonicCubicTaylorConstant n R B * ‖x - c‖ ^ 3 := by
  apply abs_sub_quadratic_taylor_le_cube_of_contDiffOn hU hf (by positivity)
    ((closedBall_subset_closedBall (by linarith : R / 8 ≤ R)).trans hball)
    (Real.sqrt_nonneg _) hx
  intro y hy i j k
  apply Real.abs_le_sqrt
  have hx' : y ∈ closedBall c (R / 2 ^ ([i,j,k] : List (Fin n)).length) := by
    convert hy using 1
    norm_num
  have h := harmonicCoordinateWord_sq_le_of_harmonicOn hU hf hh hR hball hb [i,j,k] hx'
  simpa only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    harmonicDerivativeFactor_three, div_mul_eq_mul_div] using h

/-- The original continuous viscosity-harmonic function has a uniform cubic
Taylor approximation, without a differentiability assumption on the unknown. -/
theorem IsViscosityHarmonicOn.abs_sub_quadratic_taylor_le
    {U : Set (Space n)} {f : Space n → ℝ} (hf : IsViscosityHarmonicOn U f)
    (hU : IsOpen U) {c x : Space n} {R B : ℝ} (hR : 0 < R)
    (hball : closedBall c R ⊆ U) (hb : ∀ y ∈ closedBall c R, f y ^ 2 ≤ B)
    (hx : x ∈ closedBall c (R / 8)) :
    |f x - centeredQuadratic (coordinateHessian f c) c (gradient f c) (f c) x| ≤
      harmonicCubicTaylorConstant n R B * ‖x - c‖ ^ 3 :=
  abs_sub_quadratic_taylor_le_of_harmonicOn hU (hf.contDiffOn hU)
    (fun _ hy => hf.coordinateLaplacian_eq_zero hU hy) hR hball hb hx

end KLS
end

import KLS.LocalizedMomentTransport
import KLS.CoordinateMeanValue

open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff NNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

lemma abs_le_square_of_zero_first_coordinate_jet {f : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) {c x : Space n} {M : ℝ} (hM : 0 ≤ M)
    (hzero : f c = 0) (hfirst : ∀ i, coordinateDerivative f i c = 0)
    (hsecond : ∀ y, ∀ i j, |coordinateHessian f y i j| ≤ M) :
    |f x| ≤ (n : ℝ) ^ 2 * M * ‖x-c‖ ^ 2 := by
  let d := ‖x-c‖
  have hd : 0 ≤ d := norm_nonneg _
  have hc : c ∈ closedBall c d := mem_closedBall_self hd
  have hx : x ∈ closedBall c d := by simp [d, mem_closedBall, dist_eq_norm]
  have hDb : ∀ y ∈ closedBall c d, ∀ i, |coordinateDerivative f i y| ≤ n * M * d := by
    intro y hy i
    have hs := contDiff_coordinateDerivative hf (m := 1) (by norm_num) i
    have hm := abs_sub_le_of_coordinateDerivative_le (convex_closedBall c d)
      (fun z _ => hs.differentiable (by norm_num) z) hM (fun z _ j => hsecond z j i) hc hy
    rw [hfirst, sub_zero] at hm
    exact hm.trans (mul_le_mul_of_nonneg_left (show ‖y-c‖ ≤ d from hy) (by positivity))
  have hm := abs_sub_le_of_coordinateDerivative_le (convex_closedBall c d)
    (fun z _ => hf.differentiable (by norm_num) z)
    (by positivity : 0 ≤ (n : ℝ) * M * d) hDb hc hx
  rw [hzero, sub_zero] at hm
  convert hm using 1
  dsimp [d]
  ring

/-- A genuine first-order Taylor bound from ordinary second coordinate
derivatives, proved by two applications of the mean value theorem. -/
theorem abs_first_order_taylor_remainder_le
    {f : Space n → ℝ} (hf : ContDiff ℝ 2 f) {M : ℝ} (hM : 0 ≤ M)
    (hsecond : ∀ y, ∀ i j, |coordinateHessian f y i j| ≤ M) (c x : Space n) :
    |f x - f c - inner ℝ (gradient f c) (x-c)| ≤ (n : ℝ) ^ 2 * M * ‖x-c‖ ^ 2 := by
  let q := centeredQuadratic (0 : Matrix (Fin n) (Fin n) ℝ) c (gradient f c) (f c)
  have hq : ContDiff ℝ 2 q := (contDiff_centeredQuadratic _ _ _ _).of_le (by simp)
  have hH (y : Space n) : coordinateHessian q y = 0 :=
    coordinateHessian_centeredQuadratic_of_isSymm Matrix.isSymm_zero _ _ _ _
  have hh := abs_le_square_of_zero_first_coordinate_jet (hf.sub hq) (c := c) hM
    (by simp [q]) (fun i => by
      rw [coordinateDerivative_sub (hf.differentiable (by norm_num) c)
        (hq.differentiable (by norm_num) c)]
      simp only [coordinateDerivative_eq_gradient, q,
        gradient_centeredQuadratic_of_isSymm Matrix.isSymm_zero, sub_self, map_zero, add_zero])
    (fun y i j => by
      rw [coordinateHessian_sub hf hq, hH]
      simpa using hsecond y i j) (x := x)
  have hz : (matrixAction (0 : Matrix (Fin n) (Fin n) ℝ)) (x-c) = 0 := by
    ext i
    simp [matrixAction_apply]
  convert hh using 1
  simp only [q, centeredQuadratic, hz, inner_zero_right, mul_zero, add_zero]
  congr 1
  ring

lemma exists_bound_coordinateHessian_of_hasCompactSupport
    {f : Space n → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y, ∀ i j, |coordinateHessian f y i j| ≤ M := by
  have hb : ∀ i j : Fin n, ∃ M : ℝ, ∀ y, ‖coordinateHessian f y i j‖ ≤ M := by
    intro i j
    exact (hasCompactSupport_coordinateHessian hc i j).exists_bound_of_continuous
      (contDiff_coordinateHessian hf (m := 0) (by norm_num) i j).continuous
  choose C hC using hb
  let M := ∑ i, ∑ j, |C i j|
  refine ⟨M, Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)), ?_⟩
  intro y i j
  calc
    |coordinateHessian f y i j| ≤ C i j := hC i j y
    _ ≤ |C i j| := le_abs_self _
    _ ≤ ∑ k : Fin n, |C i k| := Finset.single_le_sum (f := fun k => |C i k|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    _ ≤ M := by
      exact Finset.single_le_sum (f := fun i => ∑ j, |C i j|)
        (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (Finset.mem_univ i)

end KLS
end

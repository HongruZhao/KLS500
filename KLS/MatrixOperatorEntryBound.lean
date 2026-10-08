import KLS.DeterminantOneCorrection
import KLS.HarmonicQuadraticApproximation

open Matrix Set Metric InnerProductSpace
open scoped Topology ContDiff Matrix.Norms.Elementwise BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

lemma norm_euclidean_le_sum_abs (x : Space n) : ‖x‖ ≤ ∑ i, |x i| := by
  have he : x = ∑ i, x i • (EuclideanSpace.single i 1) := by
    ext i
    simp [Pi.single_apply]
  calc
    ‖x‖ = ‖∑ i, x i • (EuclideanSpace.single i 1)‖ := congrArg norm he
    _ ≤ ∑ i, ‖x i • (EuclideanSpace.single i 1)‖ := norm_sum_le _ _
    _ = ∑ i, |x i| := by simp [norm_smul]

/-- A deliberately coarse uniform operator bound from actual matrix entries. -/
lemma norm_matrixAction_le_of_entries_le {A : Matrix (Fin n) (Fin n) ℝ}
    {B : ℝ} (hB : 0 ≤ B) (hA : ∀ i j, |A i j| ≤ B) :
    ‖matrixAction A‖ ≤ (n : ℝ) ^ 2 * B := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  have hb (i : Fin n) : |matrixAction A x i| ≤ n * B * ‖x‖ := by
    rw [matrixAction_apply]
    calc
      |∑ j, A i j * x j| ≤ ∑ j, |A i j * x j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ : Fin n, B * ‖x‖ := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul (hA i j) (PiLp.norm_apply_le x j) (abs_nonneg _) hB
      _ = n * B * ‖x‖ := by simp [mul_assoc]
  calc
    ‖matrixAction A x‖ ≤ ∑ i, |matrixAction A x i| := norm_euclidean_le_sum_abs _
    _ ≤ ∑ _ : Fin n, (n : ℝ) * B * ‖x‖ := Finset.sum_le_sum (fun i _ => hb i)
    _ = (n : ℝ) ^ 2 * B * ‖x‖ := by simp [pow_two, mul_assoc]

/-- A positive uniform bound for the actual harmonic Taylor Hessian. -/
def harmonicTaylorHessianBound (n : ℕ) (R B : ℝ) : ℝ :=
  (n : ℝ) ^ 2 * Real.sqrt (4 * (120 + 8 * n) ^ 2 * B / R ^ 4) + 1

lemma harmonicTaylorHessianBound_pos (n : ℕ) (R B : ℝ) :
    0 < harmonicTaylorHessianBound n R B := by
  unfold harmonicTaylorHessianBound
  positivity

theorem IsViscosityHarmonicOn.norm_taylor_hessian_le
    {U : Set (Space n)} {f : Space n → ℝ} (hf : IsViscosityHarmonicOn U f)
    (hU : IsOpen U) {c : Space n} {R B : ℝ} (hR : 0 < R)
    (hball : closedBall c R ⊆ U) (hb : ∀ y ∈ closedBall c R, f y ^ 2 ≤ B) :
    ‖matrixAction (coordinateHessian f c)‖ ≤ harmonicTaylorHessianBound n R B := by
  have h := (hf.taylor_coefficients_sq_le hU hR hball hb).2.2
  have hnorm := norm_matrixAction_le_of_entries_le (Real.sqrt_nonneg _)
    (fun i j => Real.abs_le_sqrt (h i j))
  exact hnorm.trans (by unfold harmonicTaylorHessianBound; linarith)

end KLS
end

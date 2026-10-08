import KLS.HarmonicCoordinateWords
import KLS.SymmetricQuadraticCalculus
import KLS.HessianMetricEvolution

open MeasureTheory InnerProductSpace Set Filter Metric
open scoped ContDiff Topology BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

lemma norm_fderiv_le_of_coordinateDerivative_le {f : Space n → ℝ} {x : Space n}
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ i, |coordinateDerivative f i x| ≤ M) :
    ‖fderiv ℝ f x‖ ≤ n * M := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  rw [← inner_gradient_left, Real.norm_eq_abs]
  have he : inner ℝ (gradient f x) v = ∑ i, coordinateDerivative f i x * v i := by
    simp only [coordinateDerivative_eq_gradient, PiLp.inner_apply, RCLike.inner_apply,
      conj_trivial]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  calc
    |∑ i, coordinateDerivative f i x * v i| ≤ ∑ i, |coordinateDerivative f i x * v i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin n, M * ‖v‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul (hb i) (PiLp.norm_apply_le v i) (abs_nonneg _) hM
    _ = (n : ℝ) * M * ‖v‖ := by simp [mul_assoc]

lemma abs_sub_le_of_coordinateDerivative_le {f : Space n → ℝ} {S : Set (Space n)}
    (hS : Convex ℝ S) (hf : ∀ x ∈ S, DifferentiableAt ℝ f x)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x ∈ S, ∀ i, |coordinateDerivative f i x| ≤ M)
    {c x : Space n} (hc : c ∈ S) (hx : x ∈ S) :
    |f x - f c| ≤ n * M * ‖x - c‖ := by
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_fderiv_le hf
      (fun y hy => norm_fderiv_le_of_coordinateDerivative_le hM (hb y hy)) hS hc hx

end KLS
end

import KLS.StrictViscosityContact
import KLS.RegularMomentMapQuadratic

open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff RealInnerProductSpace NNReal Matrix.Norms.Elementwise
noncomputable section
namespace KLS
variable {n : ℕ}

lemma continuous_coordinateLaplacian {ψ : Space n → ℝ} (hψ : ContDiff ℝ 2 ψ) :
    Continuous (coordinateLaplacian ψ) := by
  unfold coordinateLaplacian
  exact continuous_finsetSum _ fun i _ =>
    (contDiff_coordinateHessian hψ (m := 0) (by norm_num) i i).continuous

lemma continuous_coordinateHessian_operator_norm {ψ : Space n → ℝ} (hψ : ContDiff ℝ 2 ψ) :
    Continuous (fun x => ‖matrixAction (coordinateHessian ψ x)‖) := by
  apply continuous_matrixAction.norm.comp
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (contDiff_coordinateHessian hψ (m := 0) (by norm_num) i j).continuous

lemma coordinateLaplacian_add_scalar_quadratic_const {ψ : Space n → ℝ}
    (hψ : ContDiff ℝ 2 ψ) (x₀ : Space n) (a c : ℝ) (x : Space n) :
    coordinateLaplacian (fun y => ψ y + a *
      centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) x₀ 0 0 y + c) x =
      coordinateLaplacian ψ x + a * n := by
  change (coordinateHessian _ x).trace = (coordinateHessian ψ x).trace + a * n
  rw [coordinateHessian_add_scalar_quadratic_const hψ]
  simp [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one]

lemma coordinateLaplacian_add_const (ψ : Space n → ℝ) (a : ℝ) (x : Space n) :
    coordinateLaplacian (fun y => ψ y + a) x = coordinateLaplacian ψ x := by
  change (coordinateHessian _ x).trace = (coordinateHessian ψ x).trace
  rw [coordinateHessian_add_const]

lemma coordinateHessian_neg {ψ : Space n → ℝ} (hψ : ContDiff ℝ 2 ψ) (x : Space n) :
    coordinateHessian (-ψ) x = -coordinateHessian ψ x := by
  ext i j
  change coordinateHessian (-ψ) x i j = -coordinateHessian ψ x i j
  simpa only [neg_one_smul, neg_one_mul] using coordinateHessian_smul hψ (-1) x i j

lemma coordinateLaplacian_neg {ψ : Space n → ℝ} (hψ : ContDiff ℝ 2 ψ) (x : Space n) :
    coordinateLaplacian (-ψ) x = -coordinateLaplacian ψ x := by
  change (coordinateHessian (-ψ) x).trace = -(coordinateHessian ψ x).trace
  rw [coordinateHessian_neg hψ, Matrix.trace_neg]

lemma coordinateHessian_neg_operator_norm {ψ : Space n → ℝ} (hψ : ContDiff ℝ 2 ψ) (x : Space n) :
    ‖matrixAction (coordinateHessian (-ψ) x)‖ = ‖matrixAction (coordinateHessian ψ x)‖ := by
  rw [coordinateHessian_neg hψ, ← neg_one_smul ℝ (coordinateHessian ψ x), matrixAction_smul_eq]
  simp only [norm_smul, Real.norm_eq_abs, abs_neg, abs_one, one_mul]

end KLS
end

import KLS.MomentOneStepImprovement
import KLS.AffinePotentialCutoff

open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff NNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

/-- The genuine quadratic normalization around a point and an affine jet. -/
def quadraticallyRescaledPotential (u : Space n → ℝ) (x₀ p : Space n)
    (a r : ℝ) : Space n → ℝ :=
  fun y => (u (x₀ + r • y) - a - r * inner ℝ p y) / r ^ 2

lemma quadratic_rescaling_reconstruction (u : Space n → ℝ) (x₀ p : Space n)
    (a : ℝ) {r : ℝ} (hr : r ≠ 0) (y : Space n) :
    u (x₀ + r • y) = a + r * inner ℝ p y + r ^ 2 * quadraticallyRescaledPotential u x₀ p a r y := by
  unfold quadraticallyRescaledPotential
  field_simp
  ring

lemma contDiff_quadraticallyRescaledPotential {u : Space n → ℝ} {m : ℕ∞}
    (hu : ContDiff ℝ m u) (x₀ p : Space n) (a r : ℝ) :
    ContDiff ℝ m (quadraticallyRescaledPotential u x₀ p a r) := by
  unfold quadraticallyRescaledPotential
  have hi : ContDiff ℝ m (fun y : Space n => x₀ + r • y) :=
    by fun_prop
  have hp : ContDiff ℝ m (fun y : Space n => inner ℝ p y) := contDiff_const.inner ℝ contDiff_id
  exact (((hu.comp hi).sub contDiff_const).sub (contDiff_const.mul hp)).div_const (r ^ 2)

lemma gradient_quadraticallyRescaledPotential {u : Space n → ℝ}
    (hu : Differentiable ℝ u) (x₀ p : Space n) (a : ℝ) {r : ℝ} (hr : r ≠ 0) (y : Space n) :
    gradient (quadraticallyRescaledPotential u x₀ p a r) y =
      r⁻¹ • (gradient u (x₀ + r • y) - p) := by
  have hi : HasFDerivAt (fun z : Space n => x₀ + r • z)
      (r • ContinuousLinearMap.id ℝ (Space n)) y := ((hasFDerivAt_id y).const_smul r).const_add x₀
  have hd := ((((hu (x₀ + r • y)).hasFDerivAt.comp y hi).sub_const a).sub
    ((innerSL ℝ p).hasFDerivAt.const_mul r)).mul_const ((r ^ 2)⁻¹)
  simp only [← div_eq_mul_inv] at hd
  change HasFDerivAt (quadraticallyRescaledPotential u x₀ p a r) _ y at hd
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left, hd.fderiv]
  simp only [_root_.sub_apply, ContinuousLinearMap.comp_apply,
    _root_.smul_apply, ContinuousLinearMap.id_apply, innerSL_apply_apply, real_inner_smul_left,
    inner_sub_left, inner_gradient_left, map_smul, smul_eq_mul]
  rw [real_inner_comm v p]
  field_simp

end KLS
end

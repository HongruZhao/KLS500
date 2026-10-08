import KLS.MomentPrimalDualHarmonicLimit
import KLS.HessianMetricComposition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff NNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

/-- A scalar tail primitive will be the nonnegative Laplacian test whose
scale derivative generates a compact radial averaging kernel. -/
def radialTailProfile (a : ℝ → ℝ) (s : ℝ) : ℝ := ∫ q in s..1, a q

lemma hasDerivAt_radialTailProfile {a : ℝ → ℝ} (ha : Continuous a) (s : ℝ) :
    HasDerivAt (radialTailProfile a) (-a s) s :=
  intervalIntegral.integral_hasDerivAt_left (ha.intervalIntegrable _ _)
    ha.stronglyMeasurable.stronglyMeasurableAtFilter ha.continuousAt

lemma deriv_radialTailProfile {a : ℝ → ℝ} (ha : Continuous a) :
    deriv (radialTailProfile a) = -a := by
  funext s
  exact (hasDerivAt_radialTailProfile ha s).deriv

lemma contDiff_radialTailProfile {a : ℝ → ℝ} (ha : ContDiff ℝ 1 a) :
    ContDiff ℝ 2 (radialTailProfile a) := by
  rw [show (2 : ℕ∞ω) = 1 + 1 by norm_num, contDiff_succ_iff_deriv]
  refine ⟨fun s => (hasDerivAt_radialTailProfile ha.continuous s).differentiableAt, by simp, ?_⟩
  rw [deriv_radialTailProfile ha.continuous]
  exact ha.neg

lemma deriv_deriv_radialTailProfile {a : ℝ → ℝ} (ha : ContDiff ℝ 1 a) (s : ℝ) :
    deriv (deriv (radialTailProfile a)) s = -deriv a s := by
  rw [deriv_radialTailProfile ha.continuous]
  exact (ha.differentiable (by norm_num) s).hasDerivAt.neg.deriv

lemma radialTailProfile_eq_zero {a : ℝ → ℝ} (ha0 : ∀ s, 1 ≤ s → a s = 0)
    {s : ℝ} (hs : 1 ≤ s) : radialTailProfile a s = 0 := by
  rw [radialTailProfile]
  calc
    _ = ∫ _q in s..1, (0 : ℝ) := intervalIntegral.integral_congr (fun q hq =>
      ha0 q (by rw [uIcc_of_ge hs] at hq; exact hq.1))
    _ = 0 := by simp

lemma radialTailProfile_nonneg {a : ℝ → ℝ} (ha : ∀ s, 0 ≤ a s)
    (ha0 : ∀ s, 1 ≤ s → a s = 0) (s : ℝ) : 0 ≤ radialTailProfile a s := by
  by_cases hs : s ≤ 1
  · exact intervalIntegral.integral_nonneg_of_forall hs ha
  · rw [radialTailProfile_eq_zero ha0 (le_of_not_ge hs)]

/-- Squared radial coordinate, smooth even at the center. -/
def radialSquaredCoordinate (c : Space n) (t : ℝ) (x : Space n) : ℝ := ‖x-c‖ ^ 2 / t ^ 2

lemma radialSquaredCoordinate_eq_quadratic (c : Space n) (t : ℝ) :
    radialSquaredCoordinate c t = (2 / t ^ 2) •
      centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) c 0 0 := by
  funext x
  simp only [radialSquaredCoordinate, Pi.smul_apply, smul_eq_mul,
    centeredQuadratic, inner_zero_left, zero_add, matrixAction_one_apply, real_inner_self_eq_norm_sq]
  ring

lemma contDiff_radialSquaredCoordinate (c : Space n) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (radialSquaredCoordinate c t) := by
  rw [radialSquaredCoordinate_eq_quadratic]
  exact contDiff_const.smul ((contDiff_centeredQuadratic _ _ _ _).of_le (by simp))

lemma coordinateDerivative_radialSquaredCoordinate (c x : Space n) (t : ℝ) (i : Fin n) :
    coordinateDerivative (radialSquaredCoordinate c t) i x = (2 / t ^ 2) * (x-c) i := by
  rw [radialSquaredCoordinate_eq_quadratic,
    coordinateDerivative_smul ((differentiable_centeredQuadratic _ _ _ _) x),
    coordinateDerivative_eq_gradient, gradient_centeredQuadratic Matrix.PosSemidef.one,
    matrixAction_one_apply]
  simp

lemma coordinateHessian_radialSquaredCoordinate (c x : Space n) (t : ℝ) (i : Fin n) :
    coordinateHessian (radialSquaredCoordinate c t) x i i = 2 / t ^ 2 := by
  rw [radialSquaredCoordinate_eq_quadratic,
    coordinateHessian_smul ((contDiff_centeredQuadratic _ _ _ _).of_le (by simp)),
    coordinateHessian_centeredQuadratic Matrix.PosSemidef.one]
  simp

/-- Exact radial Laplacian formula in arbitrary dimension. -/
theorem coordinateLaplacian_radialTailProfile {a : ℝ → ℝ} (ha : ContDiff ℝ 1 a)
    (c x : Space n) {t : ℝ} (ht : t ≠ 0) :
    coordinateLaplacian (fun y => radialTailProfile a (radialSquaredCoordinate c t y)) x =
      -(2 / t ^ 2) * ((n : ℝ) * a (radialSquaredCoordinate c t x) +
        2 * radialSquaredCoordinate c t x * deriv a (radialSquaredCoordinate c t x)) := by
  unfold coordinateLaplacian
  simp_rw [coordinateHessian_scalar_comp (contDiff_radialTailProfile ha)
    ((contDiff_radialSquaredCoordinate c t).of_le (by simp)),
    coordinateDerivative_radialSquaredCoordinate, coordinateHessian_radialSquaredCoordinate,
    deriv_deriv_radialTailProfile ha, deriv_radialTailProfile ha.continuous, Pi.neg_apply]
  have he : (∑ i : Fin n, (-deriv a (radialSquaredCoordinate c t x) *
      ((2 / t ^ 2) * (x-c) i) * ((2 / t ^ 2) * (x-c) i) +
      -a (radialSquaredCoordinate c t x) * (2 / t ^ 2))) =
      -deriv a (radialSquaredCoordinate c t x) * (2 / t ^ 2) ^ 2 * ‖x-c‖ ^ 2 +
        (n : ℝ) * (-a (radialSquaredCoordinate c t x) * (2 / t ^ 2)) := by
    rw [Finset.sum_add_distrib, EuclideanSpace.real_norm_sq_eq]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  dsimp only [radialSquaredCoordinate]
  field_simp
  ring

end KLS
end

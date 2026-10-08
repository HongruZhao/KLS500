import KLS.AdaptiveMaximalLocalProcess
import KLS.AdaptiveCovarianceGenerator
import KLS.CumulantBounds

/-! Genuine derivatives of the covariance as an observable of the coordinate state. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS.AdaptiveLocalization
variable {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

def coordinateCovariance (μ : Measure (Space n)) (i j : Fin n)
    (z : Fin (n+n*n) → ℝ) : ℝ := covariance μ (decodeState z).1 (decodeState z).2 i j

def coordinateScore (v : Fin (n+n*n) → ℝ) (x : Space n) : ℝ :=
  exponent (decodeState v).1 (decodeState v).2 x

theorem continuous_coordinateScore (v : Fin (n+n*n) → ℝ) : Continuous (coordinateScore v) :=
  continuous_exponent (decodeState v).1 (decodeState v).2

theorem decodeState_line (z v : Fin (n+n*n) → ℝ) (u : ℝ) :
    decodeState (z + u • v) = decodeState z + u • decodeState v := rfl

theorem coordinate_exponent_line (z v : Fin (n+n*n) → ℝ) (u : ℝ) :
    exponent (decodeState (z + u • v)).1 (decodeState (z + u • v)).2 =
      fun x => exponent (decodeState z).1 (decodeState z).2 x + u * coordinateScore v x := by
  rw [decodeState_line, exponent_line]
  rfl

def coordinateScoreBound (n : ℕ) (R : ℝ) : ℝ := (n : ℝ) * R + (n : ℝ)^2 * R^2 / 2

def coordinateCovarianceDerivativeBound (n : ℕ) (R : ℝ) : ℝ :=
  8 * R^2 * coordinateScoreBound n R

theorem coordinateScoreBound_nonneg {R : ℝ} (hR : 0 ≤ R) : 0 ≤ coordinateScoreBound n R := by
  unfold coordinateScoreBound
  positivity

theorem coordinateCovarianceDerivativeBound_nonneg {R : ℝ} (hR : 0 ≤ R) :
    0 ≤ coordinateCovarianceDerivativeBound n R := by
  exact mul_nonneg (by positivity) (coordinateScoreBound_nonneg hR)

theorem abs_coordinateScore_le {R : ℝ} (hR : 0 ≤ R) (v : Fin (n+n*n) → ℝ)
    (x : Space n) (hx : ‖x‖ ≤ R) : |coordinateScore v x| ≤ coordinateScoreBound n R * ‖v‖ := by
  have hv1 (i : Fin n) : |(decodeState v).1 i| ≤ ‖v‖ :=
    norm_le_pi_norm v (Fin.castAdd (n*n) i)
  have hv2 (i j : Fin n) : |(decodeState v).2 i j| ≤ ‖v‖ :=
    norm_le_pi_norm v (Fin.natAdd n (finProdFinEquiv (i,j)))
  have hx' (i : Fin n) : |x i| ≤ R := (PiLp.norm_apply_le x i).trans hx
  have hc : |∑ i : Fin n, (decodeState v).1 i * x i| ≤ (n : ℝ) * (‖v‖ * R) := by
    calc |∑ i : Fin n, (decodeState v).1 i * x i| ≤ ∑ i : Fin n, |(decodeState v).1 i * x i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, ‖v‖ * R := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul]
        exact mul_le_mul (hv1 i) (hx' i) (abs_nonneg _) (norm_nonneg _)
      _ = _ := by simp
  have hq : |∑ i : Fin n, ∑ j : Fin n, (decodeState v).2 i j * x i * x j| ≤
      (n : ℝ)^2 * (‖v‖ * R * R) := by
    calc |∑ i : Fin n, ∑ j : Fin n, (decodeState v).2 i j * x i * x j|
        ≤ ∑ i : Fin n, |∑ j : Fin n, (decodeState v).2 i j * x i * x j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, ‖v‖ * R * R := by
        apply Finset.sum_le_sum
        intro i _
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [abs_mul, abs_mul]
        exact mul_le_mul (mul_le_mul (hv2 i j) (hx' i) (abs_nonneg _) (norm_nonneg _))
          (hx' j) (abs_nonneg _) (mul_nonneg (norm_nonneg _) hR)
      _ = _ := by simp; ring
  calc |coordinateScore v x| ≤ |∑ i, (decodeState v).1 i * x i| +
        |(∑ i, ∑ j, (decodeState v).2 i j * x i * x j) / 2| := abs_sub _ _
    _ ≤ (n : ℝ) * (‖v‖ * R) + (n : ℝ)^2 * (‖v‖ * R * R) / 2 := by
      apply add_le_add hc
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact div_le_div_of_nonneg_right hq (by norm_num)
    _ = _ := by unfold coordinateScoreBound; ring

theorem contDiff_coordinateCovariance (hμ : IsCompact μ.support) (i j : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (coordinateCovariance μ i j) :=
  (contDiff_covariance hμ i j).comp contDiff_decodeState

theorem hasDerivAt_coordinateCovariance_line (hμ : IsCompact μ.support)
    (i j : Fin n) (z v : Fin (n+n*n) → ℝ) (u : ℝ) :
    HasDerivAt (fun a => coordinateCovariance μ i j (z + a • v))
      (tiltThirdCumulant μ (exponent (decodeState (z+u•v)).1 (decodeState (z+u•v)).2)
        (fun x => x i) (fun x => x j) (coordinateScore v)) u := by
  have hd := hasDerivAt_tilted_covariance hμ
    (continuous_exponent (decodeState z).1 (decodeState z).2)
    (f := fun x => x i) (g := fun x => x j)
    (by fun_prop) (by fun_prop) (continuous_coordinateScore v) u
  simpa only [coordinateCovariance, covariance, law, coordinate_exponent_line] using hd

def coordinateCovarianceGradient (μ : Measure (Space n)) (i j : Fin n) :
    (Fin (n+n*n) → ℝ) → (Fin (n+n*n) → ℝ) →L[ℝ] ℝ :=
  fderiv ℝ (coordinateCovariance μ i j)

def coordinateCovarianceHessian (μ : Measure (Space n)) (i j : Fin n) :
    (Fin (n+n*n) → ℝ) → (Fin (n+n*n) → ℝ) →L[ℝ] (Fin (n+n*n) → ℝ) →L[ℝ] ℝ :=
  fderiv ℝ (coordinateCovarianceGradient μ i j)

theorem hasFDerivAt_coordinateCovariance (hμ : IsCompact μ.support) (i j : Fin n)
    (z : Fin (n+n*n) → ℝ) :
    HasFDerivAt (coordinateCovariance μ i j) (coordinateCovarianceGradient μ i j z) z :=
  ((contDiff_coordinateCovariance hμ i j).differentiable (by simp) z).hasFDerivAt

theorem contDiff_coordinateCovarianceGradient (hμ : IsCompact μ.support) (i j : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (coordinateCovarianceGradient μ i j) :=
  (contDiff_coordinateCovariance hμ i j).fderiv_right (m := (⊤ : ℕ∞)) (by simp)

theorem hasFDerivAt_coordinateCovarianceGradient (hμ : IsCompact μ.support) (i j : Fin n)
    (z : Fin (n+n*n) → ℝ) :
    HasFDerivAt (coordinateCovarianceGradient μ i j) (coordinateCovarianceHessian μ i j z) z :=
  ((contDiff_coordinateCovarianceGradient hμ i j).differentiable (by simp) z).hasFDerivAt

end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.hasDerivAt_coordinateCovariance_line
#print axioms KLS.AdaptiveLocalization.abs_coordinateScore_le

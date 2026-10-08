import KLS.HarmonicBarrierComparison

/-! Scale the exact determinant remainder to arbitrary bounded smooth tests.
The positivity statement below concerns only the test Hessian. -/
open Matrix Set Metric
open scoped Topology ContDiff Matrix.Norms.Elementwise
noncomputable section
namespace KLS
variable {n : ℕ}

lemma matrixAction_smul_eq (t : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    matrixAction (t • A) = t • matrixAction A := by
  apply ContinuousLinearMap.ext
  intro x
  exact matrixAction_smul_scalar t A x

lemma determinant_remainder_bound_of_norm_le
    {H : Matrix (Fin n) (Fin n) ℝ} {B t : ℝ} (hB : 0 < B)
    (hH : ‖H‖ ≤ B) (ht : |t * B| ≤ 1) :
    |(1 + t • H).det - 1 - H.trace * t| ≤
      (nonlinearComparisonConstant n - 2) * B ^ 2 * t ^ 2 := by
  have hC := Classical.choose_spec (exists_uniform_det_identity_quadratic_bound n)
  have hM : ‖B⁻¹ • H‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hB)]
    calc
      _ ≤ B⁻¹ * B := mul_le_mul_of_nonneg_left hH (inv_nonneg.mpr hB.le)
      _ = 1 := inv_mul_cancel₀ hB.ne'
  have he := hC.2 (B⁻¹ • H) hM (t * B) ht
  have hmat : 1 + (t * B) • (B⁻¹ • H) = 1 + t • H := by
    rw [smul_smul, mul_assoc, mul_inv_cancel₀ hB.ne', mul_one]
  have htrace : (B⁻¹ • H).trace * (t * B) = H.trace * t := by
    rw [Matrix.trace_smul, smul_eq_mul]
    field_simp
  rw [hmat, htrace] at he
  convert he using 1
  dsimp [nonlinearComparisonConstant]
  ring

lemma posDef_one_add_smul_of_scaled_operator_bound
    {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsSymm) {B t : ℝ} (hB : 0 < B)
    (hHnorm : ‖matrixAction H‖ ≤ B) (ht : |t * B| ≤ 1 / 2) :
    (1 + t • H).PosDef := by
  have hscale : ‖matrixAction ((2 * B)⁻¹ • H)‖ ≤ 1 / 2 := by
    rw [matrixAction_smul_eq, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (by positivity : 0 < 2 * B))]
    calc
      _ ≤ (2 * B)⁻¹ * B := mul_le_mul_of_nonneg_left hHnorm (by positivity)
      _ = 1 / 2 := by field_simp
  have htest : |t * (2 * B)| ≤ 1 := by
    have he : t * (2 * B) = 2 * (t * B) := by ring
    rw [he, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hp := posDef_one_add_smul_of_matrixAction_norm_le_half
    (hH.smul ((2 * B)⁻¹)) hscale htest
  convert hp using 1
  rw [smul_smul, mul_assoc, mul_inv_cancel₀ (by positivity : 2 * B ≠ 0), mul_one]

end KLS
end

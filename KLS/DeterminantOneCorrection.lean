import KLS.ScaledDeterminantRemainder
import Mathlib.Topology.Order.IntermediateValue

open Matrix Set Metric InnerProductSpace
open scoped Topology ContDiff Matrix.Norms.Elementwise
noncomputable section
namespace KLS
variable {n : ℕ}

lemma norm_matrixAction_one_le (n : ℕ) :
    ‖matrixAction (1 : Matrix (Fin n) (Fin n) ℝ)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  simp only [matrixAction_one_apply, one_mul, le_refl]

lemma matrixAction_add_eq (A B : Matrix (Fin n) (Fin n) ℝ) :
    matrixAction (A + B) = matrixAction A + matrixAction B := by
  apply ContinuousLinearMap.ext
  intro x
  exact matrixAction_add_matrices A B x

/-- An actual determinant-one, positive-definite correction of a bounded
symmetric trace-zero perturbation. The correction is quadratic in epsilon. -/
theorem exists_det_one_scalar_correction (hn : 0 < n)
    {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsSymm)
    (hHnorm : ‖matrixAction H‖ ≤ 1 / 2) (htrace : H.trace = 0)
    {ε : ℝ} (hε : 0 < ε) (hεsmall : ε ≤ 1 / (2 * nonlinearComparisonConstant n)) :
    ∃ s : ℝ, |s| ≤ nonlinearComparisonConstant n * ε ^ 2 ∧
      (1 + ε • H + s • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef ∧
      (1 + ε • H + s • (1 : Matrix (Fin n) (Fin n) ℝ)).det = 1 := by
  let C := Classical.choose (exists_uniform_det_identity_quadratic_bound n)
  have hC := Classical.choose_spec (exists_uniform_det_identity_quadratic_bound n)
  have hD : nonlinearComparisonConstant n = C + 2 := rfl
  let τ := nonlinearComparisonConstant n * ε ^ 2
  have hτ : 0 ≤ τ := by dsimp [τ]; positivity [nonlinearComparisonConstant_gt_two n]
  have hgap := determinant_gaps_of_trace_zero_perturbation hn hC.1 hC.2
    ((elementwise_matrix_norm_le_matrixAction_norm H).trans hHnorm) htrace hε
    (by simpa only [hD] using hεsmall) (f := 1) (by simpa using sq_nonneg ε)
  have hlo : (1 + ε • H + (-τ) • (1 : Matrix (Fin n) (Fin n) ℝ)).det < 1 := by
    simpa only [τ, hD, neg_smul, ← sub_eq_add_neg] using hgap.1
  have hhi : 1 < (1 + ε • H + τ • (1 : Matrix (Fin n) (Fin n) ℝ)).det := by
    simpa only [τ, hD] using hgap.2
  have hcont : Continuous (fun s : ℝ =>
      (1 + ε • H + s • (1 : Matrix (Fin n) (Fin n) ℝ)).det) :=
    (continuous_const.add (continuous_id.smul continuous_const)).matrix_det
  obtain ⟨s, hs, he⟩ := intermediate_value_Icc (by linarith : -τ ≤ τ)
    hcont.continuousOn (show 1 ∈ Icc
      (1 + ε • H + (-τ) • (1 : Matrix (Fin n) (Fin n) ℝ)).det
      (1 + ε • H + τ • (1 : Matrix (Fin n) (Fin n) ℝ)).det from ⟨hlo.le,hhi.le⟩)
  have hsabs : |s| ≤ τ := abs_le.mpr hs
  refine ⟨s, hsabs, ?_, he⟩
  have hDpos : 0 < nonlinearComparisonConstant n := by
    linarith [nonlinearComparisonConstant_gt_two n]
  have heD : ε * nonlinearComparisonConstant n ≤ 1 / 2 := by
    have hh := (le_div_iff₀ (show 0 < 2 * nonlinearComparisonConstant n by positivity)).mp hεsmall
    linarith
  have hehalf : ε ≤ 1 / 2 := by
    nlinarith [nonlinearComparisonConstant_gt_two n]
  have htau : τ ≤ ε / 2 := by dsimp [τ]; nlinarith
  have hnorm : ‖matrixAction (ε • H + s • (1 : Matrix (Fin n) (Fin n) ℝ))‖ ≤ 1 / 2 := by
    rw [matrixAction_add_eq, matrixAction_smul_eq, matrixAction_smul_eq]
    calc
      _ ≤ ‖ε • matrixAction H‖ + ‖s • matrixAction (1 : Matrix (Fin n) (Fin n) ℝ)‖ := norm_add_le _ _
      _ = ε * ‖matrixAction H‖ + |s| * ‖matrixAction (1 : Matrix (Fin n) (Fin n) ℝ)‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hε]
      _ ≤ ε * (1 / 2) + τ * 1 := by gcongr; exact norm_matrixAction_one_le n
      _ ≤ 1 / 2 := by linarith
  have hp := posDef_one_add_smul_of_matrixAction_norm_le_half
    ((hH.smul ε).add (Matrix.isSymm_one.smul s)) hnorm (t := 1) (by norm_num)
  simpa only [one_smul, add_assoc] using hp


/-- The correction for an arbitrary explicit operator-norm bound. -/
theorem exists_det_one_scalar_correction_of_norm_le (hn : 0 < n)
    {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsSymm) (htrace : H.trace = 0)
    {B ε : ℝ} (hB : 0 < B) (hHnorm : ‖matrixAction H‖ ≤ B) (hε : 0 < ε)
    (hεsmall : 2 * B * ε ≤ 1 / (2 * nonlinearComparisonConstant n)) :
    ∃ s : ℝ, |s| ≤ 4 * nonlinearComparisonConstant n * B ^ 2 * ε ^ 2 ∧
      (1 + ε • H + s • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef ∧
      (1 + ε • H + s • (1 : Matrix (Fin n) (Fin n) ℝ)).det = 1 := by
  have hscale : ‖matrixAction ((2 * B)⁻¹ • H)‖ ≤ 1 / 2 := by
    rw [matrixAction_smul_eq, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (by positivity : 0 < 2 * B))]
    calc
      _ ≤ (2 * B)⁻¹ * B := mul_le_mul_of_nonneg_left hHnorm (by positivity)
      _ = 1 / 2 := by field_simp
  have hscaletrace : ((2 * B)⁻¹ • H).trace = 0 := by
    simp [Matrix.trace_smul, htrace]
  obtain ⟨s, hs, hpos, hdet⟩ := exists_det_one_scalar_correction hn
    (hH.smul ((2 * B)⁻¹)) hscale hscaletrace (by positivity : 0 < 2 * B * ε) hεsmall
  have he : (2 * B * ε) • ((2 * B)⁻¹ • H) = ε • H := by
    rw [smul_smul]
    congr 1
    field_simp
  rw [he] at hpos hdet
  refine ⟨s, ?_, hpos, hdet⟩
  convert hs using 1
  ring

end KLS
end

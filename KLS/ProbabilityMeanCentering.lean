import KLS.CenteredL2Variational
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Actual mean subtraction on a probability L² space is a bounded linear
contraction. Its squared norm is the original second moment minus the square
of the actual mean. The same identity holds for every finite Hilbert family. -/

open MeasureTheory InnerProductSpace
open scoped RealInnerProductSpace ENNReal

noncomputable section
namespace KLS.CenteredL2

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- The genuine bounded linear map subtracting the actual probability mean. -/
def centerCLM : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  ContinuousLinearMap.id ℝ _ -
    InnerProductSpace.rankOne ℝ (oneLp μ) (oneLp μ)

@[simp] theorem centerCLM_apply (u : Lp ℝ 2 μ) :
    centerCLM μ u = center μ u := by
  simp [centerCLM, center, inner_oneLp]

theorem oneLp_norm_sq : ‖oneLp μ‖ ^ 2 = 1 := by
  rw [← real_inner_self_eq_norm_sq, inner_oneLp, integral_oneLp]

/-- The probability mean is an orthogonal component of the actual L² function. -/
theorem norm_center_sq (u : Lp ℝ 2 μ) :
    ‖center μ u‖ ^ 2 = ‖u‖ ^ 2 - (∫ x, u x ∂μ) ^ 2 := by
  rw [center, norm_sub_sq_real, norm_smul, mul_pow, oneLp_norm_sq,
    real_inner_smul_right, real_inner_comm, inner_oneLp, Real.norm_eq_abs, sq_abs]
  ring

theorem norm_center_le (u : Lp ℝ 2 μ) : ‖center μ u‖ ≤ ‖u‖ := by
  have h := norm_center_sq μ u
  nlinarith [sq_nonneg (∫ x, u x ∂μ), norm_nonneg (center μ u), norm_nonneg u]

theorem norm_centerCLM_le : ‖centerCLM μ‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  simpa using norm_center_le μ u

/-- A finite family equipped with the sum of squared component L² norms. -/
abbrev Family (ι : Type*) [Fintype ι] := PiLp 2 (fun _ : ι => Lp ℝ 2 μ)

/-- Actual componentwise centering, with the genuine finite Hilbert norm. -/
def familyCenterCLM (ι : Type*) [Fintype ι] : Family μ ι →L[ℝ] Family μ ι :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => Lp ℝ 2 μ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i =>
      (centerCLM μ).comp (PiLp.proj 2 (fun _ : ι => Lp ℝ 2 μ) i)))

@[simp] theorem familyCenterCLM_apply {ι : Type*} [Fintype ι]
    (u : Family μ ι) (i : ι) : familyCenterCLM μ ι u i = center μ (u i) := by
  change centerCLM μ (u i) = _
  exact centerCLM_apply μ _

/-- The finite-family form of the exact centered-gradient identity. -/
theorem familyCenterCLM_norm_sq {ι : Type*} [Fintype ι] (u : Family μ ι) :
    ‖familyCenterCLM μ ι u‖ ^ 2 = ‖u‖ ^ 2 - ∑ i, (∫ x, u i x ∂μ) ^ 2 := by
  simp only [PiLp.norm_sq_eq_of_L2, familyCenterCLM_apply, norm_center_sq]
  rw [Finset.sum_sub_distrib]

theorem familyCenterCLM_norm_le {ι : Type*} [Fintype ι] (u : Family μ ι) :
    ‖familyCenterCLM μ ι u‖ ≤ ‖u‖ := by
  have h := familyCenterCLM_norm_sq μ u
  have hp : 0 ≤ ∑ i, (∫ x, u i x ∂μ) ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  nlinarith [norm_nonneg (familyCenterCLM μ ι u), norm_nonneg u]

theorem familyCenterCLM_opNorm_le (ι : Type*) [Fintype ι] :
    ‖familyCenterCLM μ ι‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  simpa using familyCenterCLM_norm_le μ u

end KLS.CenteredL2
end

#print axioms KLS.CenteredL2.norm_center_sq
#print axioms KLS.CenteredL2.norm_centerCLM_le
#print axioms KLS.CenteredL2.familyCenterCLM_norm_sq
#print axioms KLS.CenteredL2.familyCenterCLM_opNorm_le

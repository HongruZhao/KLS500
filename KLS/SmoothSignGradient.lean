import KLS.SmoothSignScalar

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology ContDiff ENNReal RealInnerProductSpace

noncomputable section
namespace KLS
variable {n : ℕ}

/-- The scalar chain rule identifies the actual Euclidean gradient. -/
theorem gradient_scalar_comp_real {η : ℝ → ℝ} {f : Space n → ℝ} {x : Space n}
    (hη : DifferentiableAt ℝ η (f x)) (hf : DifferentiableAt ℝ f x) :
    gradient (fun y => η (f y)) x = deriv η (f x) • gradient f x := by
  ext i
  rw [← coordinateDerivative_eq_gradient,coordinateDerivative_scalar_comp hη hf]
  simp only [PiLp.smul_apply,smul_eq_mul,coordinateDerivative_eq_gradient]

/-- Smooth bounded-gradient functions have genuine smooth sign tests, with
unit value bound, finite gradient bound, and pointwise absolute-value detection. -/
theorem exists_smooth_sign_test {h : Space n → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) {M : ℝ} (hM : 0 ≤ M)
    (hgrad : ∀ x, ‖gradient h x‖ ≤ M) {δ : ℝ} (hδ : 0 < δ) :
    ∃ g : Space n → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧
      (∀ x, |g x| ≤ 1) ∧
      (∃ L : ℝ, 0 ≤ L ∧ ∀ x, ‖gradient g x‖ ≤ L) ∧
      ∀ x, |h x| - δ ≤ h x * g x := by
  let g : Space n → ℝ := fun x => smoothSign δ (h x)
  obtain ⟨B,hB,hbound⟩ := exists_deriv_smoothSign_bound hδ
  refine ⟨g,(smoothSign_contDiff δ).comp hh,
    fun x => abs_smoothSign_le_one δ (h x),⟨B * M,mul_nonneg hB hM,?_⟩,
    fun x => abs_sub_le_mul_smoothSign hδ (h x)⟩
  intro x
  rw [gradient_scalar_comp_real
    ((smoothSign_contDiff δ).differentiable (by simp) _) (hh.differentiable (by simp) _),
    norm_smul,Real.norm_eq_abs]
  exact mul_le_mul (hbound _) (hgrad x) (norm_nonneg _) hB

end KLS
end

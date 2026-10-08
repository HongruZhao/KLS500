import KLS.WeightedResolventGradientContraction

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology ContDiff ENNReal RealInnerProductSpace

noncomputable section
namespace KLS
variable {n : ℕ}

/-- The monotone upper test leaves only the literal cutoff-gradient error
in the classical subsolution maximum argument. -/
theorem smoothUpperTest_cutoff_gradient_pairing_lower {f χ : Space n → ℝ}
    (hf : ContDiff ℝ 1 f) (hχ : ContDiff ℝ 1 χ)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1) {c : ℝ}
    (hc : ∀ x, ‖gradient χ x‖ ≤ c) (x : Space n) :
    -(2*c*‖gradient f x‖) ≤
      inner ℝ (gradient (fun y => χ y ^ 2 * smoothUpperTest f 0 y) x) (gradient f x) := by
  let ψ := smoothUpperTest f 0
  have hψ : ContDiff ℝ 1 ψ := smoothUpperTest_contDiff hf 0
  have hp0 : 0 ≤ inner ℝ (gradient ψ x) (gradient f x) := by
    rw [real_inner_comm,← sum_coordinateDerivative_mul]
    exact Finset.sum_nonneg fun i _ => smoothUpperTest_gradient_pairing_nonneg hf 0 i x
  have hpair : inner ℝ (gradient (fun y => χ y ^ 2 * ψ y) x) (gradient f x) =
      χ x ^ 2 * inner ℝ (gradient ψ x) (gradient f x) +
        2*(χ x*ψ x*inner ℝ (gradient χ x) (gradient f x)) := by
    simp only [pow_two]
    rw [gradient_mul_real (f := fun y => χ y*χ y) (g := ψ)
      ((hχ.differentiable one_ne_zero x).mul
      (hχ.differentiable one_ne_zero x)) (hψ.differentiable one_ne_zero x),
      gradient_mul_real (hχ.differentiable one_ne_zero x) (hχ.differentiable one_ne_zero x)]
    simp only [inner_add_left,inner_smul_left,conj_trivial]
    ring
  have hprod0 : 0 ≤ χ x*ψ x := mul_nonneg (hχ0 x) (smoothUpperTest_nonneg f 0 x)
  have hprod1 : χ x*ψ x ≤ 1 := by
    exact (mul_le_mul_of_nonneg_left (Real.smoothTransition.le_one _) (hχ0 x)).trans
      (by simpa using hχ1 x)
  have hi : |inner ℝ (gradient χ x) (gradient f x)| ≤ c*‖gradient f x‖ :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hc x) (norm_nonneg _))
  have he : |χ x*ψ x*inner ℝ (gradient χ x) (gradient f x)| ≤ c*‖gradient f x‖ := by
    rw [abs_mul,abs_of_nonneg hprod0]
    exact (mul_le_of_le_one_left (abs_nonneg _) hprod1).trans hi
  rw [hpair]
  have hp := mul_nonneg (sq_nonneg (χ x)) hp0
  linarith [(abs_le.mp he).1]

/-- The scalar upper-level detector is integrable and detects every positive value. -/
theorem smoothUpperTest_zero_defect {φ f : Space n → ℝ}
    (hf : Continuous f) (hI : Integrable f (potentialMeasure φ)) :
    Integrable (fun x => f x*smoothUpperTest f 0 x) (potentialMeasure φ) ∧
    (∀ x, 0 ≤ f x*smoothUpperTest f 0 x) ∧
    (∀ x, 0 < f x → 0 < f x*smoothUpperTest f 0 x) := by
  refine ⟨?_,?_,fun x hx => mul_pos hx (smoothUpperTest_pos hx)⟩
  · apply hI.norm.mono' (hf.mul (Real.smoothTransition.continuous.comp
      (hf.sub continuous_const))).aestronglyMeasurable
    exact Eventually.of_forall fun x => by
      change ‖f x*smoothUpperTest f 0 x‖ ≤ ‖f x‖
      simp only [norm_mul,Real.norm_eq_abs,abs_of_nonneg (smoothUpperTest_nonneg f 0 x)]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.smoothTransition.le_one _)
  · intro x
    by_cases hx : f x ≤ 0
    · rw [smoothUpperTest_eq_zero hx,mul_zero]
    · exact mul_nonneg (le_of_not_ge hx) (smoothUpperTest_nonneg f 0 x)

end KLS
end

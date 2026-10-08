import KLS.GradientLevelBochnerTest

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology ContDiff ENNReal

noncomputable section
namespace KLS
variable {n : ℕ}

/-- The actual upper-gradient defect detected by a bounded monotone test. -/
def gradientLevelDefect (f g : Space n → ℝ) (M : ℝ) (x : Space n) : ℝ :=
  smoothUpperTest (fun y => ‖gradient f y‖ ^ 2) (M ^ 2) x *
    (‖gradient f x‖ ^ 2 - inner ℝ (gradient g x) (gradient f x))

theorem gradientLevelDefect_continuous {f g : Space n → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (M : ℝ) :
    Continuous (gradientLevelDefect f g M) := by
  have hF := continuous_gradient_of_contDiff hf
  have hG := continuous_gradient_of_contDiff hg
  exact (Real.smoothTransition.continuous.comp ((hF.norm.pow 2).sub continuous_const)).mul
    ((hF.norm.pow 2).sub (hG.inner hF))

theorem gradientLevelDefect_nonneg {f g : Space n → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hg : ∀ x, ‖gradient g x‖ ≤ M) (x : Space n) :
    0 ≤ gradientLevelDefect f g M x := by
  have hr := norm_nonneg (gradient f x)
  have hi : inner ℝ (gradient g x) (gradient f x) ≤ M * ‖gradient f x‖ :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hg x) hr)
  by_cases hx : ‖gradient f x‖ ≤ M
  · have hs : ‖gradient f x‖ ^ 2 ≤ M ^ 2 := by nlinarith
    simp only [gradientLevelDefect,smoothUpperTest_eq_zero (f := fun y => ‖gradient f y‖ ^ 2) hs,zero_mul,le_refl]
  · exact mul_nonneg (smoothUpperTest_nonneg _ _ _) (by
      have hgt := lt_of_not_ge hx
      nlinarith)

theorem gradientLevelDefect_pos_of_gradient_gt {f g : Space n → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hg : ∀ x, ‖gradient g x‖ ≤ M) {x : Space n}
    (hx : M < ‖gradient f x‖) : 0 < gradientLevelDefect f g M x := by
  have hr := norm_nonneg (gradient f x)
  have hi : inner ℝ (gradient g x) (gradient f x) ≤ M * ‖gradient f x‖ :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hg x) hr)
  have hs : M ^ 2 < ‖gradient f x‖ ^ 2 := by nlinarith
  apply mul_pos (smoothUpperTest_pos hs)
  have hp := mul_pos (lt_of_le_of_lt hM hx) (sub_pos.mpr hx)
  nlinarith

/-- The bounded level test leaves an integrable defect whenever the actual
solution gradient is square integrable and the forcing gradient is bounded. -/
theorem gradientLevelDefect_integrable {φ f g : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) {M : ℝ}
    (hgM : ∀ x, ‖gradient g x‖ ≤ M)
    (hG : Integrable (fun x => ‖gradient f x‖ ^ 2) (potentialMeasure φ)) :
    Integrable (gradientLevelDefect f g M) (potentialMeasure φ) := by
  have hnorm : MemLp (fun x => ‖gradient f x‖) 2 (potentialMeasure φ) :=
    (memLp_two_iff_integrable_sq
      (continuous_gradient_of_contDiff hf).norm.aestronglyMeasurable).mpr hG
  have hI := hG.add ((hnorm.integrable (by norm_num)).const_mul M)
  apply hI.mono' (gradientLevelDefect_continuous hf hg M).aestronglyMeasurable
  exact Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]
    simp only [gradientLevelDefect,abs_mul,abs_of_nonneg (smoothUpperTest_nonneg _ _ _)]
    calc
      _ ≤ |‖gradient f x‖ ^ 2 - inner ℝ (gradient g x) (gradient f x)| :=
        mul_le_of_le_one_left (abs_nonneg _) (Real.smoothTransition.le_one _)
      _ ≤ ‖gradient f x‖ ^ 2 + |inner ℝ (gradient g x) (gradient f x)| := by
        have h := abs_sub_le (‖gradient f x‖ ^ 2) 0 (inner ℝ (gradient g x) (gradient f x))
        rw [sub_zero,zero_sub,abs_neg] at h
        rw [abs_of_nonneg (sq_nonneg (‖gradient f x‖))] at h
        exact h
      _ ≤ _ := add_le_add le_rfl
        ((abs_real_inner_le_norm (gradient g x) (gradient f x)).trans
          (mul_le_mul_of_nonneg_right (hgM x) (norm_nonneg _)))

end KLS
end

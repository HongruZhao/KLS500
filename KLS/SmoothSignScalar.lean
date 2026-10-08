import KLS.SmoothUpperTest

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology ContDiff ENNReal RealInnerProductSpace

noncomputable section
namespace KLS

/-- A genuine smooth sign approximation, constant outside the interval [-δ,δ]. -/
def smoothSign (δ a : ℝ) : ℝ :=
  Real.smoothTransition (a / δ) - Real.smoothTransition (-a / δ)

theorem smoothSign_contDiff (δ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (smoothSign δ) :=
  (Real.smoothTransition.contDiff.comp (contDiff_id.div_const δ)).sub
    (Real.smoothTransition.contDiff.comp (contDiff_id.neg.div_const δ))

theorem abs_smoothSign_le_one (δ a : ℝ) : |smoothSign δ a| ≤ 1 := by
  dsimp [smoothSign]
  exact abs_le.mpr ⟨by linarith [Real.smoothTransition.nonneg (a / δ),
    Real.smoothTransition.le_one (-a / δ)],
    by linarith [Real.smoothTransition.le_one (a / δ),Real.smoothTransition.nonneg (-a / δ)]⟩

theorem mul_smoothSign_nonneg {δ : ℝ} (hδ : 0 < δ) (a : ℝ) :
    0 ≤ a * smoothSign δ a := by
  by_cases ha : 0 ≤ a
  · have hz : Real.smoothTransition (-a / δ) = 0 :=
      Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) hδ.le)
    simp only [smoothSign,hz,sub_zero]
    exact mul_nonneg ha (Real.smoothTransition.nonneg _)
  · have hz : Real.smoothTransition (a / δ) = 0 :=
      Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (le_of_not_ge ha) hδ.le)
    simp only [smoothSign,hz,zero_sub,mul_neg]
    exact neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge ha)
      (Real.smoothTransition.nonneg _))

/-- The actual pairing loses at most δ, pointwise, without a convergence oracle. -/
theorem abs_sub_le_mul_smoothSign {δ : ℝ} (hδ : 0 < δ) (a : ℝ) :
    |a| - δ ≤ a * smoothSign δ a := by
  by_cases hp : δ ≤ a
  · have h1 : Real.smoothTransition (a / δ) = 1 :=
      Real.smoothTransition.one_of_one_le ((le_div_iff₀ hδ).mpr (by simpa using hp))
    have h0 : Real.smoothTransition (-a / δ) = 0 :=
      Real.smoothTransition.zero_of_nonpos
        (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le)
    simp only [smoothSign,h1,h0,sub_zero,mul_one,abs_of_nonneg (hδ.le.trans hp)]
    linarith
  · by_cases hn : a ≤ -δ
    · have h1 : Real.smoothTransition (-a / δ) = 1 :=
        Real.smoothTransition.one_of_one_le ((le_div_iff₀ hδ).mpr (by linarith))
      have h0 : Real.smoothTransition (a / δ) = 0 :=
        Real.smoothTransition.zero_of_nonpos
          (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le)
      simp only [smoothSign,h0,h1,zero_sub,mul_neg,mul_one,abs_of_nonpos (by linarith : a ≤ 0)]
      linarith
    · have habs : |a| ≤ δ := abs_le.mpr ⟨by linarith,by linarith⟩
      exact (sub_nonpos.mpr habs).trans (mul_smoothSign_nonneg hδ a)

/-- The scalar derivative is uniformly bounded; its constant may depend on δ. -/
theorem exists_deriv_smoothSign_bound {δ : ℝ} (hδ : 0 < δ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ a, |deriv (smoothSign δ) a| ≤ B := by
  obtain ⟨D,hD,hbound⟩ := exists_deriv_smoothTransition_bound
  refine ⟨2 * D / δ,by positivity,?_⟩
  intro a
  have hA := ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero (a / δ)).hasDerivAt
  have hB := ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero (-a / δ)).hasDerivAt
  have hd := (hA.comp a ((hasDerivAt_id a).div_const δ)).sub
    (hB.comp a ((hasDerivAt_id a).neg.div_const δ))
  change HasDerivAt (smoothSign δ) _ a at hd
  rw [hd.deriv]
  calc
    _ ≤ |deriv Real.smoothTransition (a / δ) * (1 / δ)| +
        |deriv Real.smoothTransition (-a / δ) * (-1 / δ)| := abs_sub _ _
    _ = |deriv Real.smoothTransition (a / δ)| / δ +
        |deriv Real.smoothTransition (-a / δ)| / δ := by
      rw [abs_mul,abs_mul,abs_div,abs_div,abs_one,abs_neg,abs_one,abs_of_pos hδ]
      ring
    _ ≤ D / δ + D / δ := add_le_add
      (div_le_div_of_nonneg_right (by simpa only [Real.norm_eq_abs] using (hbound _).2) hδ.le)
      (div_le_div_of_nonneg_right (by simpa only [Real.norm_eq_abs] using (hbound _).2) hδ.le)
    _ = _ := by ring

end KLS
end

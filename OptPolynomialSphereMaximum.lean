import OptSymmetricTensorPolynomial

/-! A nonzero real homogeneous polynomial has a signed positive radial contact. -/
open Set Metric
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS.TensorEnergy
variable {n r : ℕ}

theorem tensorPolynomial_zero (T : (Fin r → Fin n) → ℝ) (hr : 0 < r) :
    tensorPolynomial T 0 = 0 := by
  have h := tensorPolynomial_homogeneous T 0 (0 : Space n)
  simpa only [zero_smul, zero_pow (by omega : r ≠ 0), zero_mul] using h

theorem norm_normalized (x : Space n) (hx : x ≠ 0) : ‖‖x‖⁻¹ • x‖ = 1 := by
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg x)]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)

theorem tensorPolynomial_normalized (T : (Fin r → Fin n) → ℝ) (x : Space n)
    (hx : x ≠ 0) :
    tensorPolynomial T x = ‖x‖^r * tensorPolynomial T (‖x‖⁻¹ • x) := by
  have h := tensorPolynomial_homogeneous T ‖x‖ (‖x‖⁻¹ • x)
  simpa only [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul] using h

theorem exists_signed_positive_tensorPolynomial_maximum
    (T : (Fin r → Fin n) → ℝ) (hr : 0 < r)
    (hT : ∃ y : Space n, tensorPolynomial T y ≠ 0) :
    ∃ (c : ℝ) (x : Space n), (c = 1 ∨ c = -1) ∧ ‖x‖ = 1 ∧
      0 < tensorPolynomial (c • T) x ∧
      ∀ y, tensorPolynomial (c • T) y ≤ tensorPolynomial (c • T) x * ‖y‖^r := by
  obtain ⟨y, hy⟩ := hT
  have hyn : y ≠ 0 := by intro h; rw [h, tensorPolynomial_zero T hr] at hy; exact hy rfl
  have hynorm := norm_normalized y hyn
  have hs : (sphere (0 : Space n) 1).Nonempty := ⟨‖y‖⁻¹ • y, by simpa using hynorm⟩
  obtain ⟨x, hx, hmax⟩ := (isCompact_sphere (0 : Space n) 1).exists_isMaxOn hs
    (contDiff_tensorPolynomial T).continuous.abs.continuousOn
  have hxn : ‖x‖ = 1 := by simpa using hx
  have hp : 0 < |tensorPolynomial T x| := by
    have hny : tensorPolynomial T (‖y‖⁻¹ • y) ≠ 0 := by
      intro hzero
      rw [tensorPolynomial_normalized T y hyn, hzero, mul_zero] at hy
      exact hy rfl
    exact (abs_pos.mpr hny).trans_le (hmax (by simpa using hynorm))
  have hb (z : Space n) : |tensorPolynomial T z| ≤ |tensorPolynomial T x| * ‖z‖^r := by
    by_cases hz : z = 0
    · simp [hz, tensorPolynomial_zero T hr, zero_pow (by omega : r ≠ 0)]
    · rw [tensorPolynomial_normalized T z hz, abs_mul,
        abs_of_nonneg (pow_nonneg (norm_nonneg z) r), mul_comm]
      exact mul_le_mul_of_nonneg_right (hmax (by simpa using norm_normalized z hz))
        (pow_nonneg (norm_nonneg z) r)
  by_cases hpx : 0 ≤ tensorPolynomial T x
  · refine ⟨1, x, Or.inl rfl, hxn, ?_, ?_⟩
    · simpa only [one_smul, abs_of_nonneg hpx] using hp
    · intro z
      simpa only [one_smul, abs_of_nonneg hpx] using (le_abs_self (tensorPolynomial T z)).trans (hb z)
  · have hpx' : tensorPolynomial T x ≤ 0 := le_of_not_ge hpx
    refine ⟨-1, x, Or.inr rfl, hxn, ?_, ?_⟩
    · simpa only [tensorPolynomial_smul, neg_one_mul, abs_of_nonpos hpx'] using hp
    · intro z
      simpa only [tensorPolynomial_smul, neg_one_mul, abs_of_nonpos hpx'] using
        (neg_le_abs (tensorPolynomial T z)).trans (hb z)

end KLS.TensorEnergy
end

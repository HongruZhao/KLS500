import KLS.ContinuousViscosityDistribution

open MeasureTheory InnerProductSpace Set Filter Metric
open scoped Topology NNReal ContDiff
noncomputable section
namespace KLS
variable {n : ℕ}

lemma IsViscosityHarmonicOn.upper_test {U : Set (Space n)} {w : Space n → ℝ}
    (hw : IsViscosityHarmonicOn U w) {x : Space n} (hx : x ∈ U)
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ 2 ψ)
    (hm : IsLocalMax (fun y => w y - ψ y) x) :
    0 ≤ coordinateLaplacian ψ x := by
  let d := w x - ψ x
  have hc : w x = (fun y => ψ y + d) x := by dsimp [d]; ring
  have ht : ∀ᶠ y in 𝓝 x, w y ≤ ψ y + d := by
    filter_upwards [hm] with y hy
    dsimp [d]
    linarith
  have h := (hw.2 x hx (fun y => ψ y + d) (hψ.add contDiff_const) hc).1 ht
  simpa only [coordinateLaplacian_add_const] using h

lemma IsViscosityHarmonicOn.neg {U : Set (Space n)} {w : Space n → ℝ}
    (hw : IsViscosityHarmonicOn U w) : IsViscosityHarmonicOn U (-w) := by
  refine ⟨hw.1.neg, ?_⟩
  intro x hx ψ hψ hc
  have hc' : w x = (-ψ) x := by change -w x = ψ x at hc; simp only [Pi.neg_apply]; linarith
  have h := hw.2 x hx (-ψ) hψ.neg hc'
  constructor
  · intro ht
    have ht' : ∀ᶠ y in 𝓝 x, (-ψ) y ≤ w y := by
      filter_upwards [ht] with y hy
      change -w y ≤ ψ y at hy
      change -ψ y ≤ w y
      linarith
    have hh := h.2 ht'
    rw [coordinateLaplacian_neg hψ] at hh
    linarith
  · intro ht
    have ht' : ∀ᶠ y in 𝓝 x, w y ≤ (-ψ) y := by
      filter_upwards [ht] with y hy
      change ψ y ≤ -w y at hy
      change w y ≤ -ψ y
      linarith
    have hh := h.1 ht'
    rw [coordinateLaplacian_neg hψ] at hh
    linarith

/-- No regularity of the viscosity-harmonic function beyond continuity is
assumed. Its pairing with the concrete Laplacian of every nonnegative compact
C2 test supported on an interior ball vanishes. -/
theorem IsViscosityHarmonicOn.integral_mul_laplacian_eq_zero
    {U : Set (Space n)} {w : Space n → ℝ} (hw : IsViscosityHarmonicOn U w)
    {c : Space n} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hball : closedBall c R ⊆ U)
    {φ : Space n → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ ball c r) (hφ0 : ∀ x, 0 ≤ φ x) :
    (∫ x, w x * coordinateLaplacian φ x) = 0 := by
  have hlo := integral_mul_laplacian_nonneg_of_continuous_upper_tests_on_ball hr hrR
    (hw.1.mono hball) (fun x hx ψ hψ hm => hw.upper_test (hball hx) (hψ.of_le (by simp)) hm)
    hφ hφc hφs hφ0
  have hhi := integral_mul_laplacian_nonneg_of_continuous_upper_tests_on_ball hr hrR
    (hw.neg.1.mono hball) (fun x hx ψ hψ hm => hw.neg.upper_test (hball hx) (hψ.of_le (by simp)) hm)
    hφ hφc hφs hφ0
  simp only [Pi.neg_apply, neg_mul, integral_neg] at hhi
  linarith

end KLS
end

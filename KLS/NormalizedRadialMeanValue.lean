import KLS.RadialAverageLimit

open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff NNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

def radialBaseBump : ContDiffBump (0 : ℝ) := ⟨1/4, 1/2, by norm_num, by norm_num⟩

def radialKernelMass (n : ℕ) : ℝ := ∫ y : Space n, radialBaseBump (‖y‖ ^ 2)

def normalizedRadialProfile (n : ℕ) (s : ℝ) : ℝ := radialBaseBump s * (radialKernelMass n)⁻¹

lemma radialBaseBump_eq_zero {s : ℝ} (hs : 1 ≤ s) : radialBaseBump s = 0 := by
  apply radialBaseBump.zero_of_le_dist
  simp only [radialBaseBump, Real.dist_eq, sub_zero]
  have hpos : 0 ≤ s := by linarith
  rw [abs_of_nonneg hpos]
  linarith

lemma radialKernelMass_pos (n : ℕ) : 0 < radialKernelMass n := by
  let κ : Space n → ℝ := fun y => radialBaseBump (‖y‖ ^ 2)
  have he : κ = radialAverageKernel radialBaseBump 0 1 := by
    funext y
    simp [κ, radialAverageKernel, radialSquaredCoordinate]
  have hc : Continuous κ := by rw [he]; exact (contDiff_radialAverageKernel radialBaseBump.contDiff 0 1).continuous
  have hs : tsupport κ ⊆ closedBall (0 : Space n) 1 := by
    rw [he]
    exact tsupport_radialAverageKernel_subset_closedBall (fun _ hh => radialBaseBump_eq_zero hh) 0 zero_lt_one
  have hcomp : HasCompactSupport κ :=
    (isCompact_closedBall (0 : Space n) 1).of_isClosed_subset (isClosed_tsupport _) hs
  have hzero : κ 0 ≠ 0 := by
    have hz : radialBaseBump 0 = 1 := radialBaseBump.one_of_mem_closedBall
      (mem_closedBall_self radialBaseBump.rIn_pos.le)
    simpa only [κ, norm_zero, zero_pow (by decide : 2 ≠ 0), hz] using (one_ne_zero : (1 : ℝ) ≠ 0)
  exact hc.integral_pos_of_hasCompactSupport_nonneg_nonzero hcomp
    (fun _ => radialBaseBump.nonneg) hzero

lemma normalizedRadialProfile_contDiff (n : ℕ) : ContDiff ℝ 1 (normalizedRadialProfile n) :=
  radialBaseBump.contDiff.mul contDiff_const

lemma normalizedRadialProfile_nonneg (n : ℕ) (s : ℝ) : 0 ≤ normalizedRadialProfile n s :=
  mul_nonneg radialBaseBump.nonneg (inv_nonneg.mpr (radialKernelMass_pos n).le)

lemma normalizedRadialProfile_eq_zero (n : ℕ) {s : ℝ} (hs : 1 ≤ s) :
    normalizedRadialProfile n s = 0 := by
  rw [normalizedRadialProfile, radialBaseBump_eq_zero hs, zero_mul]

lemma integral_normalizedRadialProfile (n : ℕ) :
    (∫ y : Space n, normalizedRadialProfile n (‖y‖ ^ 2)) = 1 := by
  unfold normalizedRadialProfile
  rw [integral_mul_const]
  exact mul_inv_cancel₀ (radialKernelMass_pos n).ne'

lemma integral_normalizedRadialKernel (c : Space n) {t : ℝ} (ht : 0 < t) :
    (∫ x, radialAverageKernel (normalizedRadialProfile n) c t x) = 1 := by
  have hh := integral_radialAverageKernel_eq_rescaled (fun _ => (1 : ℝ))
    (normalizedRadialProfile n) c ht
  simpa only [one_mul, integral_normalizedRadialProfile] using hh

/-- A normalized, nonnegative compact C1 radial kernel gives a genuine local
mean-value inequality for any continuous distribution subharmonic function. -/
theorem subharmonic_le_normalizedRadialAverage {u : Space n → ℝ} (hu : Continuous u)
    {c : Space n} {t R : ℝ} (ht : 0 < t) (htR : t < R)
    (hdist : ∀ ψ : Space n → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ ball c R → (∀ x, 0 ≤ ψ x) →
      0 ≤ ∫ x, u x * coordinateLaplacian ψ x) :
    u c ≤ ∫ x, u x * radialAverageKernel (normalizedRadialProfile n) c t x := by
  have hh := subharmonic_le_radialAverage hu (normalizedRadialProfile_contDiff n)
    (fun _ hs => normalizedRadialProfile_eq_zero n hs) (normalizedRadialProfile_nonneg n) ht htR hdist
  simpa only [integral_normalizedRadialProfile, mul_one] using hh

end KLS
end

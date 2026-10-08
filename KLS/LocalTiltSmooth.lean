import KLS.LocalTiltNumeratorDerivative

open MeasureTheory InnerProductSpace Set Filter Metric
open scoped ContDiff Topology BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

theorem contDiffOn_tiltNumerator_nat_of_localNormExponentialDomain
    {μ : Measure (Space n)} {f : Space n → ℝ} {r : ℝ}
    (hf : LocalNormExponentialDomain μ f r) (k : ℕ) :
    ContDiffOn ℝ k (tiltNumerator μ (fun _ => 0) f) (ball 0 r) := by
  induction k generalizing f with
  | zero =>
    rw [Nat.cast_zero, contDiffOn_zero]
    intro z hz
    exact (hasFDerivAt_tiltNumerator_coordinate_of_localNormExponentialDomain hf
      (by simpa only [mem_ball, dist_zero_right] using hz)).continuousAt.continuousWithinAt
  | succ k ih =>
    have hd (z : Space n) (hz : z ∈ ball (0 : Space n) r) :
        HasFDerivAt (tiltNumerator μ (fun _ => 0) f)
          (∑ i, tiltNumerator μ (fun _ => 0) (fun x => f x * x i) z •
            (EuclideanSpace.proj i : Space n →L[ℝ] ℝ)) z :=
      hasFDerivAt_tiltNumerator_coordinate_of_localNormExponentialDomain hf
        (by simpa only [mem_ball, dist_zero_right] using hz)
    rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_fderiv_of_isOpen isOpen_ball]
    refine ⟨fun z hz => (hd z hz).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    have hs : ContDiffOn ℝ k
        (fun z => ∑ i, tiltNumerator μ (fun _ => 0) (fun x => f x * x i) z •
          (EuclideanSpace.proj i : Space n →L[ℝ] ℝ)) (ball 0 r) := by
      apply ContDiffOn.sum
      intro i _
      exact (ih (hf.mul_coordinate i)).smul contDiffOn_const
    exact hs.congr (fun z hz => (hd z hz).fderiv)

theorem contDiffOn_tiltNumerator_of_localNormExponentialDomain
    {μ : Measure (Space n)} {f : Space n → ℝ} {r : ℝ}
    (hf : LocalNormExponentialDomain μ f r) :
    ContDiffOn ℝ (⊤ : ℕ∞) (tiltNumerator μ (fun _ => 0) f) (ball 0 r) :=
  contDiffOn_infty.mpr (contDiffOn_tiltNumerator_nat_of_localNormExponentialDomain hf)

theorem contDiffAt_laplace_of_localNormExponentialDomain {μ : Measure (Space n)}
    {r : ℝ} (hf : LocalNormExponentialDomain μ (fun _ => 1) r)
    {z : Space n} (hz : ‖z‖ < r) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun w => tiltPartition μ (fun x => inner ℝ w x)) z := by
  have hc := (contDiffOn_tiltNumerator_of_localNormExponentialDomain hf).contDiffAt
    (isOpen_ball.mem_nhds (by simpa only [mem_ball, dist_zero_right] using hz))
  convert hc using 1
  funext w
  simp only [tiltNumerator, tiltPartition, zero_add, one_mul]

theorem contDiffAt_logLaplace_of_localNormExponentialDomain {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] {r : ℝ} (hf : LocalNormExponentialDomain μ (fun _ => 1) r)
    {z : Space n} (hz : ‖z‖ < r) :
    ContDiffAt ℝ (⊤ : ℕ∞) (tiltLogLaplace μ) z := by
  have hi : Integrable (fun x => Real.exp (inner ℝ z x)) μ := by
    simpa only [one_mul] using hf.integrable_tilt hz.le
  exact (contDiffAt_laplace_of_localNormExponentialDomain hf hz).log
    (integral_exp_pos hi).ne'

end KLS
end

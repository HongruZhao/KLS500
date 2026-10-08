import KLS.LogConcavityLocalExponential
import KLS.LocalExponentialFromOneRate
import KLS.LocalTiltNumeratorMoments

/-! Genuine local smoothness and coordinate Laplace jets of arbitrary
compact-set log-concave probability measures, with no all-rate assumption. -/
open MeasureTheory InnerProductSpace Filter Metric
open scoped ContDiff Topology BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

theorem measureLogConcave.exists_localNormExponentialDomain_one
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : measureLogConcave μ) :
    ∃ r : ℝ, 0 < r ∧ LocalNormExponentialDomain μ (fun _ => 1) r := by
  obtain ⟨b, hb, hi⟩ := hμ.exists_pos_integrable_exp_norm
  exact ⟨b / 2, by positivity, localNormExponentialDomain_of_one_rate
    aestronglyMeasurable_const (by simpa only [norm_one, one_mul] using hi) (by linarith)⟩

theorem measureLogConcave.contDiffAt_laplace
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : measureLogConcave μ) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun z => tiltPartition μ (fun x => inner ℝ z x)) 0 := by
  obtain ⟨r, hr, hd⟩ := hμ.exists_localNormExponentialDomain_one
  exact contDiffAt_laplace_of_localNormExponentialDomain hd (by simpa using hr)

theorem measureLogConcave.contDiffAt_logLaplace
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : measureLogConcave μ) :
    ContDiffAt ℝ (⊤ : ℕ∞) (tiltLogLaplace μ) 0 := by
  obtain ⟨r, hr, hd⟩ := hμ.exists_localNormExponentialDomain_one
  exact contDiffAt_logLaplace_of_localNormExponentialDomain hd (by simpa using hr)

theorem measureLogConcave.iteratedFDeriv_laplace_coordinate_moment
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : measureLogConcave μ)
    {d : ℕ} (a : Fin d → Fin n) :
    iteratedFDeriv ℝ d (fun z => tiltPartition μ (fun x => inner ℝ z x)) 0
      (fun j => EuclideanSpace.single (a j) 1) = ∫ x, ∏ j, x (a j) ∂μ := by
  obtain ⟨r, hr, hd⟩ := hμ.exists_localNormExponentialDomain_one
  have he : (fun z => tiltPartition μ (fun x => inner ℝ z x)) =
      tiltNumerator μ (fun _ => 0) (fun _ => 1) := by
    funext z
    simp only [tiltPartition, tiltNumerator, zero_add, one_mul]
  rw [he, iteratedFDeriv_tiltNumerator_moment_of_local hd (by simpa using hr)]
  simp only [one_mul, inner_zero_left, Real.exp_zero, mul_one,
    EuclideanSpace.inner_single_right]
  simp

end KLS
end

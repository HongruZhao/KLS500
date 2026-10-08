import KLS.VarianceGradientDomain
import KLS.FullPoincareStrongApproximation

open MeasureTheory Set Filter
open scoped Topology ContDiff ENNReal NNReal

noncomputable section
namespace KLS
variable {n : ℕ}

/-- Actual damping and whitening reduce smooth global convex laws to smooth
strongly convex laws for the same smooth variance criterion. -/
theorem admissibleMeasure.smoothVarianceBound_of_strongDensity_of_smooth_global
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {V : Space n → ℝ} (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hc : ConvexOn ℝ univ V)
    (heq : μ = potentialMeasure V) {K : ℝ}
    (hstrong : ∀ ν : Measure (Space n), admissibleMeasure ν →
      HasSmoothStronglyConvexDensity ν → SmoothCompactVarianceGradientBound ν K) :
    SmoothCompactVarianceGradientBound μ K := by
  let : IsProbabilityMeasure μ := hμ.isProb
  let ν := fun k => quadraticDamping μ (cutoffScale k)
  let : ∀ k, IsProbabilityMeasure (ν k) := fun k =>
    isProbabilityMeasure_quadraticDamping_nonneg μ (cutoffScale_pos k).le
  let : ∀ k, IsProbabilityMeasure (whitenedMeasure (ν k)) := fun _ => inferInstance
  apply smoothCompactVarianceGradientBound_of_weak_measure_limit
    (ν := fun k => whitenedMeasure (ν k))
  · filter_upwards [eventually_admissible_global_strongDensity_whitened_damping hμ
      (fun k => (cutoffScale_pos k).le) cutoffScale_tendsto_zero hV hc heq cutoffScale_pos]
      with k hk
    exact hstrong _ hk.1 hk.2
  · exact fun _ hf hs => hμ.tendsto_integral_whitened_quadraticDamping_compact
      (fun k => (cutoffScale_pos k).le) cutoffScale_tendsto_zero hf hs

/-- Actual isotropic Gaussian smoothing and damped whitening extend one
uniform smooth variance criterion to every compact admissible law. -/
theorem admissibleMeasure.smoothVarianceBound_of_strongDensity_of_compact
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ) (hs : IsCompact μ.support)
    {K : ℝ}
    (hstrong : ∀ ν : Measure (Space n), admissibleMeasure ν →
      HasSmoothStronglyConvexDensity ν → SmoothCompactVarianceGradientBound ν K) :
    SmoothCompactVarianceGradientBound μ K := by
  let : IsProbabilityMeasure μ := hμ.isProb
  apply smoothCompactVarianceGradientBound_of_weak_measure_limit
    (ν := fun k => KLS.isotropicGaussianSmoothing μ (cutoffScale k))
  · exact Eventually.of_forall fun k =>
      (hμ.isotropicGaussianSmoothing (cutoffScale_pos k).ne').smoothVarianceBound_of_strongDensity_of_smooth_global
        (isotropicGaussianPotential_contDiff hs (cutoffScale_pos k).ne')
        (hμ.isotropicGaussianPotential_convex hs (cutoffScale_pos k).ne')
        (hμ.isotropicGaussianSmoothing_eq_exp_potential hs (cutoffScale_pos k).ne') hstrong
  · exact fun _ hf hc => tendsto_integral_isotropicGaussianSmoothing_compact μ hf hc

/-- Actual isotropic compact cutoffs, Gaussian smoothing, damping, and
whitening transfer the same criterion to the full original admissible class. -/
theorem admissibleMeasure.smoothVarianceBound_of_global_strongDensity
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ) {K : ℝ}
    (hstrong : ∀ ν : Measure (Space n), admissibleMeasure ν →
      HasSmoothStronglyConvexDensity ν → SmoothCompactVarianceGradientBound ν K) :
    SmoothCompactVarianceGradientBound μ K := by
  let : IsProbabilityMeasure μ := hμ.isProb
  obtain ⟨R, _, hR, hevent⟩ := hμ.exists_whitened_compact_cutoffs
  let : ∀ k, IsProbabilityMeasure (ballCutoffMeasure μ R k) := fun k =>
    isProbabilityMeasure_ballCutoffMeasure hR k
  let : ∀ k, IsProbabilityMeasure (whitenedBallCutoffMeasure μ R k) := fun k =>
    inferInstanceAs (IsProbabilityMeasure (whitenedMeasure (ballCutoffMeasure μ R k)))
  apply smoothCompactVarianceGradientBound_of_weak_measure_limit
    (ν := fun k => whitenedBallCutoffMeasure μ R k)
  · filter_upwards [hevent] with k hk
    exact hk.1.smoothVarianceBound_of_strongDensity_of_compact hk.2 hstrong
  · exact fun _ hf hc => hμ.tendsto_integral_whitenedBallCutoffMeasure_compact hR hf hc

/-- The same full-class reduction yields the complete bounded locally
Lipschitz criterion, using proved absolute continuity of admissible laws. -/
theorem admissibleMeasure.boundedVarianceBound_of_global_strongDensity
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ) {K : ℝ}
    (hstrong : ∀ ν : Measure (Space n), admissibleMeasure ν →
      HasSmoothStronglyConvexDensity ν → SmoothCompactVarianceGradientBound ν K) :
    BoundedVarianceGradientBound μ K := by
  let : IsProbabilityMeasure μ := hμ.isProb
  exact boundedVarianceGradientBound_of_smooth_compact hμ.absolutelyContinuousLebesgue
    (hμ.smoothVarianceBound_of_global_strongDensity hstrong)

end KLS
end

import KLS.WhitenedCutoffWeakLimit
import KLS.GaussianWeakMeasureApproximation
import KLS.IsotropicGaussianGradient

/-! An actual-law reduction of the full faithful class to global smooth uniformly convex laws. -/
open MeasureTheory Set Filter
open scoped Topology ContDiff NNReal
noncomputable section
namespace KLS
variable {n : ℕ}

theorem admissibleMeasure.mem_poincareConstants_of_strongDensity_of_smooth_global
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {V : Space n → ℝ} (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hc : ConvexOn ℝ univ V)
    (heq : μ = potentialMeasure V) {C : ℝ≥0} (hC : 0 < C)
    (hstrong : ∀ ν : Measure (Space n), admissibleMeasure ν →
      HasSmoothStronglyConvexDensity ν → C ∈ poincareConstants ν) :
    C ∈ poincareConstants μ := by
  let : IsProbabilityMeasure μ := hμ.isProb
  let ν := fun k => quadraticDamping μ (cutoffScale k)
  let : ∀ k, IsProbabilityMeasure (ν k) := fun k =>
    isProbabilityMeasure_quadraticDamping_nonneg μ (cutoffScale_pos k).le
  let : ∀ k, IsProbabilityMeasure (whitenedMeasure (ν k)) := fun _ => inferInstance
  apply mem_poincareConstants_of_weak_measure_limit hμ.absolutelyContinuousLebesgue hC
    (ν := fun k => whitenedMeasure (ν k))
  · filter_upwards [eventually_admissible_global_strongDensity_whitened_damping hμ
      (fun k => (cutoffScale_pos k).le) cutoffScale_tendsto_zero hV hc heq cutoffScale_pos] with k hk
    exact hstrong _ hk.1 hk.2
  · exact fun _ hf hs => hμ.tendsto_integral_whitened_quadraticDamping_compact
      (fun k => (cutoffScale_pos k).le) cutoffScale_tendsto_zero hf hs

/-- Every property of the approximating laws is proved from the actual cutoff,
Gaussian smoothing, nonnegative damping and covariance whitening operations.
The one remaining inequality premise is exactly the full faithful bound on
global smooth uniformly convex isotropic probability laws. -/
theorem admissibleMeasure.mem_poincareConstants_of_global_strongDensity
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ) {C : ℝ≥0} (hC : 0 < C)
    (hstrong : ∀ ν : Measure (Space n), admissibleMeasure ν →
      HasSmoothStronglyConvexDensity ν → C ∈ poincareConstants ν) :
    C ∈ poincareConstants μ := by
  apply hμ.mem_poincareConstants_of_compact_laws hC
  intro ρ hρ hs
  let : IsProbabilityMeasure ρ := hρ.isProb
  apply mem_poincareConstants_of_isotropicGaussianSmoothing hρ.absolutelyContinuousLebesgue hC
  exact Eventually.of_forall fun k =>
    (hρ.isotropicGaussianSmoothing (cutoffScale_pos k).ne').mem_poincareConstants_of_strongDensity_of_smooth_global
      (isotropicGaussianPotential_contDiff hs (cutoffScale_pos k).ne')
      (hρ.isotropicGaussianPotential_convex hs (cutoffScale_pos k).ne')
      (hρ.isotropicGaussianSmoothing_eq_exp_potential hs (cutoffScale_pos k).ne') hC hstrong

end KLS
end

import KLS.VarianceL1CutoffExtension
import KLS.PoincareWeakMeasureLimit

open MeasureTheory Set Filter
open scoped Topology ContDiff ENNReal NNReal

noncomputable section
namespace KLS
variable {n : ℕ}

/-- A uniform bound on actual variance for bounded locally Lipschitz tests,
using the integral of their actual gradient. -/
def BoundedVarianceGradientBound (μ : Measure (Space n)) (K : ℝ) : Prop :=
  ∀ f : Space n → ℝ, LocallyLipschitz f → Integrable (gradient f) μ →
    ∀ B : ℝ, 0 ≤ B → (∀ x, |f x| ≤ B) →
      ProbabilityTheory.variance f μ ≤ K * B * (∫ x, ‖gradient f x‖ ∂μ)

/-- The same actual inequality restricted to smooth compact tests. -/
def SmoothCompactVarianceGradientBound (μ : Measure (Space n)) (K : ℝ) : Prop :=
  ∀ f : Space n → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
    ∀ B : ℝ, 0 ≤ B → (∀ x, |f x| ≤ B) →
      ProbabilityTheory.variance f μ ≤ K * B * (∫ x, ‖gradient f x‖ ∂μ)

/-- Actual convergence on continuous compact tests passes the smooth variance
criterion to the limiting probability law without changing its constant. -/
theorem smoothCompactVarianceGradientBound_of_weak_measure_limit
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    {ν : ℕ → Measure (Space n)} [∀ k, IsProbabilityMeasure (ν k)] {K : ℝ}
    (hbound : ∀ᶠ k in atTop, SmoothCompactVarianceGradientBound (ν k) K)
    (hlim : ∀ f : Space n → ℝ, Continuous f → HasCompactSupport f →
      Tendsto (fun k => ∫ x, f x ∂ν k) atTop (𝓝 (∫ x, f x ∂μ))) :
    SmoothCompactVarianceGradientBound μ K := by
  intro f hf hc B hB hfB
  have hf2 (ρ : Measure (Space n)) [IsProbabilityMeasure ρ] : MemLp f 2 ρ :=
    hf.continuous.memLp_of_hasCompactSupport hc
  have hvar : Tendsto (fun k => ProbabilityTheory.variance f (ν k)) atTop
      (𝓝 (ProbabilityTheory.variance f μ)) := by
    have ht := (hlim (fun x => f x ^ 2) (hf.continuous.pow 2)
      (by simpa only [pow_two, Pi.mul_def] using hc.mul_right)).sub
        ((hlim f hf.continuous hc).pow 2)
    simpa only [ProbabilityTheory.variance_eq_sub (hf2 _), Pi.pow_apply] using ht
  have hgrad := hlim (fun x => ‖gradient f x‖)
    (continuous_gradient_of_contDiff (hf.of_le (by simp) : ContDiff ℝ 1 f)).norm
    (hasCompactSupport_gradient hc).norm
  apply le_of_tendsto_of_tendsto hvar (hgrad.const_mul (K * B))
  filter_upwards [hbound] with k hk
  exact hk f hf hc B hB hfB

end KLS
end

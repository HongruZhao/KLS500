import KLS.BoundedL1PairingLimit
import KLS.WeakMomentSublevelSequence

open MeasureTheory Set Filter
open scoped ContDiff Topology NNReal ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- The actual original-weak-potential cutoff sequence has vanishing errors
 against every bounded measurable observable. The actual cutoff operator,
 all integrability, and the limit are derived from literal weak transport. -/
theorem weak_moment_exists_cutoffs_with_bounded_observable_errors
    {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hconv : ConvexOn ℝ univ u) (hV : ContDiff ℝ 1 V) (hVc : ConvexOn ℝ univ V)
    {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun p => V p - (κ / 2) * ‖p‖ ^ 2))
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K) :
    ∃ x₀ : Space n, (∀ x, u x₀ ≤ u x) ∧
      (∀ k, ContDiff ℝ 1 (hessianMetricCutoffSequence u x₀ k) ∧
        HasCompactSupport (hessianMetricCutoffSequence u x₀ k) ∧
        ∀ x, hessianMetricCutoffSequence u x₀ k x ∈ Icc (0 : ℝ) 1) ∧
      (∀ x, Monotone (fun k => hessianMetricCutoffSequence u x₀ k x)) ∧
      (∀ x, Tendsto (fun k => hessianMetricCutoffSequence u x₀ k x) atTop (𝓝 1)) ∧
      (∀ k, Integrable (hessianMetricDiffusion u V (hessianMetricCutoffSequence u x₀ k))
        (potentialMeasure u)) ∧
      (Tendsto (fun k => ∫ x, ‖hessianMetricDiffusion u V (hessianMetricCutoffSequence u x₀ k) x‖
        ∂potentialMeasure u) atTop (𝓝 0)) ∧
      ∀ S : Space n → ℝ, AEStronglyMeasurable S (potentialMeasure u) →
        ∀ C : ℝ, (∀ᵐ x ∂potentialMeasure u, ‖S x‖ ≤ C) →
          (∀ k, Integrable (fun x => S x*hessianMetricDiffusion u V
            (hessianMetricCutoffSequence u x₀ k) x) (potentialMeasure u)) ∧
          Tendsto (fun k => ∫ x, S x*hessianMetricDiffusion u V
            (hessianMetricCutoffSequence u x₀ k) x ∂potentialMeasure u) atTop (𝓝 0) := by
  obtain ⟨x₀,hmin,hcut,hmono,hpoint,hLi,hLlim⟩ := weak_moment_exists_hessianMetricCutoffSequence
    hLip hconv hV hVc hκ hstrong hK hKc hpush
  refine ⟨x₀,hmin,hcut,hmono,hpoint,hLi,hLlim,?_⟩
  intro S hS C hC
  exact bounded_pairing_tendsto_zero_of_integral_norm hS hC hLi hLlim

end KLS
end

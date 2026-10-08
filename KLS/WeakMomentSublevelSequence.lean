import KLS.WeakMomentSublevelBound

open MeasureTheory Set Filter
open scoped ContDiff Topology NNReal ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- The actual original weak potential has a concrete monotone C1 compact
 sublevel-cutoff sequence tending to one, with genuine diffusion integrable
 at every step and its L1 error tending to zero. No classical C2 source,
 assumed cutoff sequence, drift integrability or energy estimate is used. -/
theorem weak_moment_exists_hessianMetricCutoffSequence
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
      Tendsto (fun k => ∫ x, ‖hessianMetricDiffusion u V (hessianMetricCutoffSequence u x₀ k) x‖
        ∂potentialMeasure u) atTop (𝓝 0) := by
  have hu := moment_contDiff_one_closedTarget hLip hconv hV.continuous hK hKc hpush
  obtain ⟨x₀,hmin⟩ := exists_minimizer_of_finite_potentialMeasure hLip.continuous hconv
  obtain ⟨C,_,hderiv⟩ := sublevelCutoffProfile_deriv_bounded
  have hbound (k : ℕ) := weak_moment_potentialSublevelCutoff_L1_bound
    hLip hconv hV hVc hκ hstrong hK hKc hpush x₀ (cutoffScale_pos k) hderiv
  refine ⟨x₀,hmin,?_,hessianMetricCutoffSequence_monotone hmin,
    hessianMetricCutoffSequence_tendsto_one u x₀,fun k => (hbound k).1,?_⟩
  · intro k
    exact ⟨potentialSublevelCutoff_contDiff_one hu x₀ (cutoffScale k),
      potentialSublevelCutoff_hasCompactSupport hLip.continuous hconv x₀ (cutoffScale_pos k),
      fun x => potentialSublevelCutoff_mem_Icc u x₀ x (cutoffScale k)⟩
  · apply squeeze_zero (fun k => integral_nonneg (fun x => norm_nonneg _))
      (fun k => (hbound k).2)
    simpa only [zero_mul] using (cutoffScale_tendsto_zero.mul_const
      (∫ x, ‖hessianMetricDiffusion u V (potentialHeight u x₀) x‖ ∂potentialMeasure u)).mul_const
        (C+∫ s, ‖deriv (deriv sublevelCutoffProfile) s‖)

end KLS
end

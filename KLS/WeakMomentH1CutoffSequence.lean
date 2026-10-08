import KLS.WeakMomentH1CutoffTransfer
import KLS.WeakMomentBoundedCutoffErrors

open MeasureTheory Set Filter Matrix
open scoped ContDiff Topology NNReal ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- The original weak potential supplies actual compact cutoffs whose
 inverse-Hessian flux pairings with every bounded local H1 observable tend
 to zero. The exact negative diffusion identity is derived at every step. -/
theorem weak_moment_exists_cutoffs_with_H1_flux_errors
    {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : ContDiff ℝ 1 V) (hVc : ConvexOn ℝ univ V)
    {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun p => V p - (κ / 2) * ‖p‖ ^ 2))
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K) :
    ∃ x₀ : Space n, (∀ x, u x₀ ≤ u x) ∧
      (∀ k, ContDiff ℝ 1 (hessianMetricCutoffSequence u x₀ k) ∧
        HasCompactSupport (hessianMetricCutoffSequence u x₀ k) ∧
        ∀ x, hessianMetricCutoffSequence u x₀ k x ∈ Icc (0 : ℝ) 1) ∧
      (∀ k j, LocallyLipschitz (coordinateDerivative (hessianMetricCutoffSequence u x₀ k) j)) ∧
      (∀ x, Monotone (fun k => hessianMetricCutoffSequence u x₀ k x)) ∧
      (∀ x, Tendsto (fun k => hessianMetricCutoffSequence u x₀ k x) atTop (𝓝 1)) ∧
      ∀ (S : Space n → ℝ) (F : Fin n → Space n → ℝ),
        (∀ E : Set (Space n), IsCompact E → MemLp S 2 (volume.restrict E)) →
        ∀ C : ℝ, (∀ᵐ x ∂volume, ‖S x‖ ≤ C) →
        (∀ i E, IsCompact E → MemLp (F i) 2 (volume.restrict E)) →
        (∀ i, HasLocalWeakCoordinateDerivative S (F i) i) →
        (∀ k, Integrable (fun x => ∑ i, ∑ j, (coordinateHessian u x)⁻¹ i j * F i x *
            coordinateDerivative (hessianMetricCutoffSequence u x₀ k) j x) (potentialMeasure u) ∧
          Integrable (fun x => S x * hessianMetricDiffusion u V (hessianMetricCutoffSequence u x₀ k) x)
            (potentialMeasure u) ∧
          (∫ x, ∑ i, ∑ j, (coordinateHessian u x)⁻¹ i j * F i x *
            coordinateDerivative (hessianMetricCutoffSequence u x₀ k) j x ∂potentialMeasure u) =
            -(∫ x, S x * hessianMetricDiffusion u V (hessianMetricCutoffSequence u x₀ k) x
              ∂potentialMeasure u)) ∧
        Tendsto (fun k => ∫ x, ∑ i, ∑ j, (coordinateHessian u x)⁻¹ i j * F i x *
          coordinateDerivative (hessianMetricCutoffSequence u x₀ k) j x ∂potentialMeasure u) atTop (𝓝 0) := by
  obtain ⟨x₀,hmin,hcut,hmono,hpoint,_,_,herror⟩ :=
    weak_moment_exists_cutoffs_with_bounded_observable_errors hLip hc hV hVc hκ hstrong hK hKc hpush
  have hu := moment_contDiff_one_closedTarget hLip hc hV.continuous hK hKc hpush
  have hG := weak_moment_gradient_lipschitz_of_uniformlyConvex_target
    hLip hc hV hVc hκ hstrong hK hKc hpush
  have hDχ (k : ℕ) (j : Fin n) :
      LocallyLipschitz (coordinateDerivative (hessianMetricCutoffSequence u x₀ k) j) :=
    coordinateDerivative_potentialSublevelCutoff_locallyLipschitz hu hG x₀ (cutoffScale k) j
  refine ⟨x₀,hmin,hcut,hDχ,hmono,hpoint,?_⟩
  intro S F hS C hbound hFloc hF
  have htransfer (k : ℕ) := weak_moment_hessianMetricDiffusion_bounded_local_H1_transfer
    hLip hc hV hVc hκ hstrong hK hKc hpush (hDχ k) (hcut k).2.1 hS hbound hFloc hF
  refine ⟨htransfer,?_⟩
  have hac : potentialMeasure u ≪ volume := withDensity_absolutelyContinuous _ _
  have hSm : AEStronglyMeasurable S (potentialMeasure u) :=
    (locallyIntegrable_of_memLp_two_on_compacts hS).aestronglyMeasurable.mono_ac hac
  have hlim := (herror S hSm C (hbound.filter_mono hac.ae_le)).2.neg
  have he : (fun k => ∫ x, ∑ i, ∑ j, (coordinateHessian u x)⁻¹ i j * F i x *
      coordinateDerivative (hessianMetricCutoffSequence u x₀ k) j x ∂potentialMeasure u) =
      fun k => -(∫ x, S x * hessianMetricDiffusion u V (hessianMetricCutoffSequence u x₀ k) x
        ∂potentialMeasure u) := funext fun k => (htransfer k).2.2
  rw [he]
  simpa only [neg_zero] using hlim

end KLS
end

import KLS.WeakMomentRawTraceLocalIntegrability

open MeasureTheory Set Matrix
open scoped ContDiff ENNReal NNReal
noncomputable section
namespace KLS
variable {n : ℕ}

/-- A single actual weak third tensor supplied by weak transport has locally
 integrable raw trace energies for every constant matrix. The Hessian weak
 derivative identities are retained. No energy is assumed globally L1. -/
theorem weak_moment_exists_third_tensor_with_local_trace_energy
    {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : ContDiff ℝ 2 V) (hVc : ConvexOn ℝ univ V)
    {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun p => V p - (κ / 2) * ‖p‖ ^ 2))
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K) :
    ∃ T : Space n → Fin n → Matrix (Fin n) (Fin n) ℝ,
      (∀ k i j S, IsCompact S → MemLp (fun x => T x k i j) 2 (volume.restrict S)) ∧
      (∀ k i j, HasLocalWeakCoordinateDerivative
        (fun x => coordinateHessian u x i j) (fun x => T x k i j) k) ∧
      ∀ B : Matrix (Fin n) (Fin n) ℝ,
        LocallyIntegrable (fun x => rawHessianTraceGradientTerm (coordinateHessian u x) B (T x)) volume ∧
        LocallyIntegrable (fun x => rawHessianTraceTargetTerm
          (coordinateHessian u x) (coordinateHessian V (gradient u x)) B) volume ∧
        LocallyIntegrable (fun x => rawHessianTraceThirdTerm (coordinateHessian u x) B (T x)) volume := by
  obtain ⟨T,hT,hTw⟩ := weak_moment_exists_third_tensor
    hLip hc (hV.of_le (by norm_num)) hVc hκ hstrong hK hKc hpush
  exact ⟨T,hT,hTw,fun B => weak_moment_rawTrace_locallyIntegrable
    hLip hc hV hVc hκ hstrong hK hKc hpush hT B⟩

/-- Local L1 trace terms are measurable in the actual source measure, and
 their sum is integrable against every actual continuous compact cutoff. -/
theorem rawTrace_potential_measurable_and_compact_integrable
    {u A F D : Space n → ℝ} (hu : Continuous u)
    (hA : LocallyIntegrable A volume) (hF : LocallyIntegrable F volume)
    (hD : LocallyIntegrable D volume) :
    AEStronglyMeasurable A (potentialMeasure u) ∧
    AEStronglyMeasurable F (potentialMeasure u) ∧
    AEStronglyMeasurable D (potentialMeasure u) ∧
    ∀ χ : Space n → ℝ, Continuous χ → HasCompactSupport χ →
      Integrable (fun x => χ x * (A x + F x + D x)) (potentialMeasure u) := by
  refine ⟨aestronglyMeasurable_potential_of_locallyIntegrable hA,
    aestronglyMeasurable_potential_of_locallyIntegrable hF,
    aestronglyMeasurable_potential_of_locallyIntegrable hD,?_⟩
  intro χ hχ hχc
  exact integrable_compact_mul_potential_of_locallyIntegrable hu ((hA.add hF).add hD) hχ hχc

end KLS
end

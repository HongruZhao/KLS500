import KLS.WeakMomentLocalEssentialBounds

open MeasureTheory Set Filter Matrix
open scoped ContDiff Topology ENNReal NNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- Actual weak-moment transport and local L2 tensor entries suffice for the
 local L1 trace energies. Target curvature here requires a C2 target. -/
theorem weak_moment_rawTrace_locallyIntegrable
    {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : ContDiff ℝ 2 V) (hVc : ConvexOn ℝ univ V)
    {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun p => V p - (κ / 2) * ‖p‖ ^ 2))
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    {T : Space n → Fin n → Matrix (Fin n) (Fin n) ℝ}
    (hT : ∀ k i j S, IsCompact S → MemLp (fun x => T x k i j) 2 (volume.restrict S))
    (B : Matrix (Fin n) (Fin n) ℝ) :
    LocallyIntegrable (fun x => rawHessianTraceGradientTerm (coordinateHessian u x) B (T x)) volume ∧
    LocallyIntegrable (fun x => rawHessianTraceTargetTerm
      (coordinateHessian u x) (coordinateHessian V (gradient u x)) B) volume ∧
    LocallyIntegrable (fun x => rawHessianTraceThirdTerm (coordinateHessian u x) B (T x)) volume := by
  have hV1 : ContDiff ℝ 1 V := hV.of_le (by norm_num)
  have hG := weak_moment_gradient_lipschitz_of_uniformlyConvex_target
    hLip hc hV1 hVc hκ hstrong hK hKc hpush
  have hAe := weak_moment_ae_hessian_equation_of_gradient_lipschitz
    hLip hc hV.continuous hK hKc hpush hG
  have hAe' : ∀ᵐ x ∂(volume : Measure (Space n)), (coordinateHessian u x).PosDef ∧
      (coordinateHessian u x).det = Real.exp (-u x + V (gradient u x)) :=
    hAe.mono fun _ hx => ⟨hx.1,hx.2.1⟩
  have hH (S : Set (Space n)) := memLp_coordinateHessian_top_of_gradient_lipschitz hG (volume.restrict S)
  have hJ (S : Set (Space n)) (hS : IsCompact S) :=
    memLp_inverseHessian_top_on_compact_of_ae_equation hLip hG hV.continuous hAe' hS
  have hM (S : Set (Space n)) (hS : IsCompact S) (i j : Fin n) :=
    memLp_continuous_top_on_compact
      (((contDiff_coordinateHessian hV (m := 0) (by norm_num) i j).continuous).comp hG.continuous) hS
  refine ⟨locallyIntegrable_iff.mpr ?_,locallyIntegrable_iff.mpr ?_,locallyIntegrable_iff.mpr ?_⟩
  · intro S hS
    exact memLp_one_iff_integrable.mp
      (memLp_rawHessianTraceGradientTerm (hJ S hS) (fun k i j => hT k i j S hS) B)
  · intro S hS
    have : IsFiniteMeasure (volume.restrict S) := ⟨by simpa using hS.measure_lt_top⟩
    exact memLp_one_iff_integrable.mp
      ((memLp_rawHessianTraceTargetTerm_top (hH S) (hM S hS) B).mono_exponent (by simp))
  · intro S hS
    exact memLp_one_iff_integrable.mp
      (memLp_rawHessianTraceThirdTerm (hH S) (hJ S hS) (fun k i j => hT k i j S hS) B)

/-- Local Lebesgue integrability gives an actual measurable representative
 in the source potential measure. -/
theorem aestronglyMeasurable_potential_of_locallyIntegrable
    {u f : Space n → ℝ} (hf : LocallyIntegrable f volume) :
    AEStronglyMeasurable f (potentialMeasure u) :=
  hf.aestronglyMeasurable.mono_ac (withDensity_absolutelyContinuous _ _)

/-- Actual continuous compact tests pair integrably with any locally L1
 function in a continuous source potential measure. -/
theorem integrable_compact_mul_potential_of_locallyIntegrable
    {u f χ : Space n → ℝ} (hu : Continuous u) (hf : LocallyIntegrable f volume)
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) :
    Integrable (fun x => χ x * f x) (potentialMeasure u) := by
  apply (integrable_potentialMeasure_iff hu.measurable).mpr
  have he : Continuous (fun x => χ x * Real.exp (-u x)) := hχ.mul (Real.continuous_exp.comp hu.neg)
  have hi := hf.integrable_smul_left_of_hasCompactSupport he hχc.mul_right
  simpa only [smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using hi

end KLS
end

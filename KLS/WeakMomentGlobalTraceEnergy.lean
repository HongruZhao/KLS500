import KLS.WeakMomentTracePositivity

open MeasureTheory Set Filter Matrix
open scoped ContDiff Topology NNReal ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- The remaining localized trace-balance interface, stated literally in
 terms of the actual Hessian, raw weak tensor and compact C1 tests. This
 predicate is an explicit premise until the Hessian-evolution contraction
 theorem supplies it. It contains no global energy integrability premise. -/
def RawTraceLocalizedBalance (u V : Space n → ℝ)
    (T : Space n → Fin n → Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ χ : Space n → ℝ, ContDiff ℝ 1 χ → HasCompactSupport χ →
    (∫ x, χ x * (rawHessianTraceGradientTerm (coordinateHessian u x) B (T x) +
      rawHessianTraceTargetTerm (coordinateHessian u x) (coordinateHessian V (gradient u x)) B +
      rawHessianTraceThirdTerm (coordinateHessian u x) B (T x)) ∂potentialMeasure u) =
    (∫ x, χ x * rawHessianTraceSquare (coordinateHessian u x) B ∂potentialMeasure u) -
      (1 / 2 : ℝ) * ∫ x, ∑ i, ∑ j, (coordinateHessian u x)⁻¹ i j *
        (2 * (B * coordinateHessian u x * B * T x i).trace) * coordinateDerivative χ j x
        ∂potentialMeasure u

/-- Original-source trace energies are globally integrable and satisfy the
 certified half-trace estimate once the explicit actual localized balance
 holds. All other inputs, including cutoff errors and tensor comparison,
 are derived. Positive Fatou precedes the final dominated-convergence step. -/
theorem weak_moment_trace_energy_of_localized_balance
    {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : ContDiff ℝ 2 V) (hVc : ConvexOn ℝ univ V)
    {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun p => V p - (κ / 2) * ‖p‖ ^ 2))
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    {T : Space n → Fin n → Matrix (Fin n) (Fin n) ℝ}
    (hTl : ∀ k i j E, IsCompact E → MemLp (fun x => T x k i j) 2 (volume.restrict E))
    (hTw : ∀ k i j, HasLocalWeakCoordinateDerivative
      (fun x => coordinateHessian u x i j) (fun x => T x k i j) k)
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.PosSemidef)
    (hbalance : RawTraceLocalizedBalance u V T B) :
    Integrable (fun x => rawHessianTraceSquare (coordinateHessian u x) B) (potentialMeasure u) ∧
    Integrable (fun x => rawHessianTraceGradientTerm (coordinateHessian u x) B (T x)) (potentialMeasure u) ∧
    Integrable (fun x => rawHessianTraceTargetTerm
      (coordinateHessian u x) (coordinateHessian V (gradient u x)) B) (potentialMeasure u) ∧
    Integrable (fun x => rawHessianTraceThirdTerm (coordinateHessian u x) B (T x)) (potentialMeasure u) ∧
    (∫ x, rawHessianTraceSquare (coordinateHessian u x) B ∂potentialMeasure u) =
      (∫ x, rawHessianTraceGradientTerm (coordinateHessian u x) B (T x) ∂potentialMeasure u) +
      (∫ x, rawHessianTraceTargetTerm (coordinateHessian u x) (coordinateHessian V (gradient u x)) B
        ∂potentialMeasure u) +
      (∫ x, rawHessianTraceThirdTerm (coordinateHessian u x) B (T x) ∂potentialMeasure u) ∧
    (∫ x, rawHessianTraceGradientTerm (coordinateHessian u x) B (T x) ∂potentialMeasure u) ≤
      (1 / 2 : ℝ) * ∫ x, rawHessianTraceSquare (coordinateHessian u x) B ∂potentialMeasure u := by
  let S := fun x => rawHessianTraceSquare (coordinateHessian u x) B
  let A := fun x => rawHessianTraceGradientTerm (coordinateHessian u x) B (T x)
  let F := fun x => rawHessianTraceTargetTerm (coordinateHessian u x) (coordinateHessian V (gradient u x)) B
  let D := fun x => rawHessianTraceThirdTerm (coordinateHessian u x) B (T x)
  let dS : Fin n → Space n → ℝ := fun i x => 2 * (B * coordinateHessian u x * B * T x i).trace
  have hV1 : ContDiff ℝ 1 V := hV.of_le (by norm_num)
  have hG := weak_moment_gradient_lipschitz_of_uniformlyConvex_target hLip hc hV1 hVc hκ hstrong hK hKc hpush
  have hH (μ : Measure (Space n)) := memLp_coordinateHessian_top_of_gradient_lipschitz hG μ
  have hStop : MemLp S ∞ volume := rawHessianTraceSquare_memLp_top (hH volume) B
  have hSi : Integrable S (potentialMeasure u) :=
    (rawHessianTraceSquare_memLp_top (hH (potentialMeasure u)) B).integrable (by simp)
  have hSloc (E : Set (Space n)) (hE : IsCompact E) : MemLp S 2 (volume.restrict E) := by
    have : IsFiniteMeasure (volume.restrict E) := ⟨by simpa using hE.measure_lt_top⟩
    exact (rawHessianTraceSquare_memLp_top (hH (volume.restrict E)) B).mono_exponent (by simp)
  have hdSloc (i : Fin n) (E : Set (Space n)) (hE : IsCompact E) :
      MemLp (dS i) 2 (volume.restrict E) :=
    rawHessianTraceSquare_derivative_memLp_two (hH (volume.restrict E)) (fun a b => hTl i a b E hE) B
  have hdS (i : Fin n) : HasLocalWeakCoordinateDerivative S (dS i) i :=
    hasLocalWeakCoordinateDerivative_rawHessianTraceSquare (hTw i)
      (fun a b E _ => hH (volume.restrict E) a b) (hTl i) B
  obtain ⟨x₀,_,hcut,_,_,hpoint,htransfer⟩ :=
    weak_moment_exists_cutoffs_with_H1_flux_errors hLip hc hV1 hVc hκ hstrong hK hKc hpush
  let χ := hessianMetricCutoffSequence u x₀
  have hflux := htransfer S dS hSloc (lpNorm S ∞ volume) (ae_le_lpNorm_exponent_top hStop) hdSloc hdS
  let error := fun k => -(1 / 2 : ℝ) * ∫ x, ∑ i, ∑ j, (coordinateHessian u x)⁻¹ i j *
    dS i x * coordinateDerivative (χ k) j x ∂potentialMeasure u
  have herror : Tendsto error atTop (𝓝 0) := by
    simpa only [mul_zero] using hflux.2.const_mul (-(1 / 2 : ℝ))
  obtain ⟨hAl,hFl,hDl⟩ := weak_moment_rawTrace_locallyIntegrable hLip hc hV hVc hκ hstrong hK hKc hpush hTl B
  obtain ⟨hAm,hFm,hDm,hcompact⟩ := rawTrace_potential_measurable_and_compact_integrable
    hLip.continuous hAl hFl hDl
  have hnonneg := weak_moment_rawTrace_nonneg_and_comparison hLip hc hV hVc hκ hstrong hK hKc hpush hTl hTw hB
  have hχm (k : ℕ) : AEStronglyMeasurable (χ k) (potentialMeasure u) :=
    (hcut k).1.continuous.aestronglyMeasurable
  have hχrange (k : ℕ) : ∀ᵐ x ∂potentialMeasure u, 0 ≤ χ k x ∧ χ k x ≤ 1 :=
    Eventually.of_forall (hcut k).2.2
  have hχlim : ∀ᵐ x ∂potentialMeasure u, Tendsto (fun k => χ k x) atTop (𝓝 1) :=
    Eventually.of_forall hpoint
  have hχint (k : ℕ) : Integrable (fun x => χ k x * (A x + F x + D x)) (potentialMeasure u) :=
    hcompact (χ k) (hcut k).1.continuous (hcut k).2.1
  have hbal (k : ℕ) : (∫ x, χ k x * (A x + F x + D x) ∂potentialMeasure u) =
      (∫ x, χ k x * S x ∂potentialMeasure u) + error k := by
    simpa only [A,F,D,S,dS,χ,error,sub_eq_add_neg,neg_mul] using hbalance (χ k) (hcut k).1 (hcut k).2.1
  exact ⟨hSi,trace_energy_integrability_and_half_of_cutoff_balance hSi hAm hFm hDm
    (hnonneg.mono fun _ hx => hx.1) (hnonneg.mono fun _ hx => hx.2.1)
    (hnonneg.mono fun _ hx => hx.2.2.1) (hnonneg.mono fun _ hx => hx.2.2.2)
    hχm hχrange hχlim hχint herror hbal⟩

end KLS
end

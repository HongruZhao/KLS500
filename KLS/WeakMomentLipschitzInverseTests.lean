import KLS.LocalL2CompactPairings

open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped Topology ContDiff NNReal ENNReal Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- Compact restrictions of a genuine continuous scalar coefficient are L2. -/
theorem memLp_continuous_on_compact
    {b : Space n → ℝ} (hb : Continuous b) {S : Set (Space n)} (hS : IsCompact S) :
    MemLp b 2 (volume.restrict S) := by
  have : IsFiniteMeasure (volume.restrict S) := ⟨by simpa using hS.measure_lt_top⟩
  simpa only [mul_one] using memLp_continuous_mul_on_compact hS
    (memLp_const (1 : ℝ) (μ := volume.restrict S) (p := 2)) hb

/-- The actual weighted inverse-Hessian flux is locally L2. The proof uses
 the literal a.e. MA identity and the bounded actual adjugate. -/
theorem memLp_weighted_inverseHessian_on_compact_of_ae_equation
    {u V : Space n → ℝ} {L G : ℝ≥0} (hLip : LipschitzWith L u)
    (hG : LipschitzWith G (gradient u)) (hV : Continuous V)
    (hAe : ∀ᵐ x ∂(volume : Measure (Space n)), (coordinateHessian u x).PosDef ∧
      (coordinateHessian u x).det = Real.exp (-u x + V (gradient u x)))
    {S : Set (Space n)} (hS : IsCompact S) (i j : Fin n) :
    MemLp (fun x => Real.exp (-u x)*(coordinateHessian u x)⁻¹ i j) 2 (volume.restrict S) := by
  have ht := memLp_continuous_mul_on_compact hS
    (memLp_adjugateHessian_on_compact_of_gradient_lipschitz hLip hG hS i j)
    (Real.continuous_exp.comp (hV.comp hG.continuous).neg)
  apply MemLp.ae_eq (hf_Lp := ht)
  filter_upwards [ae_restrict_of_ae hAe] with x hx
  exact exp_neg_target_mul_adjugate_eq_exp_neg_source_mul_inverse hx.1 hx.2 i j

/-- The genuine weak inverse-Hessian divergence remains valid for compact
 locally Lipschitz tests, with their actual a.e. derivatives. -/
theorem weak_moment_inverseHessian_integral_column_locallyLipschitz_volume
    {u V ψ : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : ContDiff ℝ 1 V) (hVc : ConvexOn ℝ univ V)
    {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun p => V p - (κ / 2) * ‖p‖ ^ 2))
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    (hψ : LocallyLipschitz ψ) (hψc : HasCompactSupport ψ) (j : Fin n) :
    (∑ i, ∫ x, Real.exp (-u x)*(coordinateHessian u x)⁻¹ i j*coordinateDerivative ψ i x) =
      ∫ x, Real.exp (-u x)*coordinateDerivative V j (gradient u x)*ψ x := by
  have hG := weak_moment_gradient_lipschitz_of_uniformlyConvex_target
    hLip hc hV hVc hκ hstrong hK hKc hpush
  have hAe := weak_moment_ae_hessian_equation_of_gradient_lipschitz hLip hc hV.continuous hK hKc hpush hG
  exact integral_divergence_of_locallyLipschitz_test
    (fun i S hS => memLp_weighted_inverseHessian_on_compact_of_ae_equation hLip hG hV.continuous
      (hAe.mono (fun _ hx => ⟨hx.1,hx.2.1⟩)) hS i j)
    (fun S hS => memLp_continuous_on_compact
      ((Real.continuous_exp.comp hLip.continuous.neg).mul
        (((contDiff_coordinateDerivative hV (m := 0) (by norm_num) j).continuous).comp hG.continuous)) hS)
    (fun φ hφ hφc => weak_moment_inverseHessian_integral_column_volume
      hLip hc hV hVc hκ hstrong hK hKc hpush hφ hφc j) hψ hψc

/-- The same compact locally Lipschitz test identity in the actual source
 potential measure. -/
theorem weak_moment_inverseHessian_integral_column_locallyLipschitz
    {u V ψ : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : ContDiff ℝ 1 V) (hVc : ConvexOn ℝ univ V)
    {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun p => V p - (κ / 2) * ‖p‖ ^ 2))
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    (hψ : LocallyLipschitz ψ) (hψc : HasCompactSupport ψ) (j : Fin n) :
    (∑ i, ∫ x, (coordinateHessian u x)⁻¹ i j*coordinateDerivative ψ i x ∂potentialMeasure u) =
      ∫ x, coordinateDerivative V j (gradient u x)*ψ x ∂potentialMeasure u := by
  simpa only [integral_potentialMeasure hLip.continuous.measurable,mul_comm,mul_left_comm,mul_assoc] using
    weak_moment_inverseHessian_integral_column_locallyLipschitz_volume
      hLip hc hV hVc hκ hstrong hK hKc hpush hψ hψc j

end KLS
end

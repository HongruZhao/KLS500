import KLS.WeakEllipticH1CutoffTransfer
import KLS.WeakMomentFirstFactor

open MeasureTheory Set Filter Matrix
open scoped ContDiff Topology NNReal ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- In the actual weak source measure, a compact C1,1 cutoff pairs its
 inverse-Hessian gradient against a bounded local H1 observable with exactly
 minus the actual cutoff diffusion pairing. Both integrabilities are derived. -/
theorem weak_moment_hessianMetricDiffusion_bounded_local_H1_transfer
    {u V χ S : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : ContDiff ℝ 1 V) (hVc : ConvexOn ℝ univ V)
    {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun p => V p - (κ / 2) * ‖p‖ ^ 2))
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    (hDχ : ∀ j, LocallyLipschitz (coordinateDerivative χ j)) (hχc : HasCompactSupport χ)
    {F : Fin n → Space n → ℝ}
    (hS : ∀ E : Set (Space n), IsCompact E → MemLp S 2 (volume.restrict E))
    {C : ℝ} (hbound : ∀ᵐ x ∂volume, ‖S x‖ ≤ C)
    (hFloc : ∀ i E, IsCompact E → MemLp (F i) 2 (volume.restrict E))
    (hF : ∀ i, HasLocalWeakCoordinateDerivative S (F i) i) :
    Integrable (fun x => ∑ i, ∑ j, (coordinateHessian u x)⁻¹ i j *
      F i x * coordinateDerivative χ j x) (potentialMeasure u) ∧
    Integrable (fun x => S x * hessianMetricDiffusion u V χ x) (potentialMeasure u) ∧
    (∫ x, ∑ i, ∑ j, (coordinateHessian u x)⁻¹ i j * F i x * coordinateDerivative χ j x
      ∂potentialMeasure u) = -(∫ x, S x * hessianMetricDiffusion u V χ x ∂potentialMeasure u) := by
  have hG := weak_moment_gradient_lipschitz_of_uniformlyConvex_target
    hLip hc hV hVc hκ hstrong hK hKc hpush
  have hAe := weak_moment_ae_hessian_equation_of_gradient_lipschitz hLip hc hV.continuous hK hKc hpush hG
  let A : Space n → Matrix (Fin n) (Fin n) ℝ := fun x => Real.exp (-u x) • (coordinateHessian u x)⁻¹
  let b : Fin n → Space n → ℝ := fun j x => Real.exp (-u x) * coordinateDerivative V j (gradient u x)
  have hA (i j : Fin n) (E : Set (Space n)) (hE : IsCompact E) :
      MemLp (fun x => A x i j) 2 (volume.restrict E) :=
    memLp_weighted_inverseHessian_on_compact_of_ae_equation hLip hG hV.continuous
      (hAe.mono (fun _ hx => ⟨hx.1,hx.2.1⟩)) hE i j
  have hb (j : Fin n) (E : Set (Space n)) (hE : IsCompact E) :
      MemLp (b j) 2 (volume.restrict E) :=
    memLp_continuous_on_compact
      ((Real.continuous_exp.comp hLip.continuous.neg).mul
        (((contDiff_coordinateDerivative hV (m := 0) (by norm_num) j).continuous).comp hG.continuous)) hE
  have hdiv (j : Fin n) (ψ : Space n → ℝ) (hψ : LocallyLipschitz ψ) (hψc : HasCompactSupport ψ) :
      (∑ i, ∫ x, A x i j * coordinateDerivative ψ i x) = ∫ x, b j x * ψ x :=
    weak_moment_inverseHessian_integral_column_locallyLipschitz_volume
      hLip hc hV hVc hκ hstrong hK hKc hpush hψ hψc j
  obtain ⟨hi,hSi,he⟩ := integral_weakEllipticFlux_bounded_local_H1
    hA hb hdiv hDχ hχc hS hbound hFloc hF
  have hop (x : Space n) : weakEllipticExpression A b χ x =
      Real.exp (-u x) * hessianMetricDiffusion u V χ x :=
    weakEllipticExpression_weighted_inverseHessian u V χ x
  have hpoint (x : Space n) : (∑ i, weakEllipticFlux A χ i x * F i x) =
      (∑ i, ∑ j, (coordinateHessian u x)⁻¹ i j * F i x * coordinateDerivative χ j x) * Real.exp (-u x) := by
    simp only [weakEllipticFlux,A,Matrix.smul_apply,smul_eq_mul,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hsum := integrable_finsetSum Finset.univ (fun i _ => hi i)
  refine ⟨(integrable_potentialMeasure_iff hLip.continuous.measurable).mpr ?_,
    (integrable_potentialMeasure_iff hLip.continuous.measurable).mpr ?_,?_⟩
  · simpa only [hpoint] using hsum
  · simpa only [hop,mul_assoc,mul_comm,mul_left_comm] using hSi
  · rw [← integral_finsetSum _ (fun i _ => hi i)] at he
    simp_rw [hpoint,hop] at he
    simpa only [integral_potentialMeasure hLip.continuous.measurable,
      mul_assoc,mul_comm,mul_left_comm] using he

end KLS
end

import KLS.FiniteTraceBalance
import KLS.WeakMomentHessianEvolution
import KLS.WeakHessianMatrixTest
import KLS.WeakMomentLocalTraceTensor
import KLS.RawWeakTraceDerivative
import KLS.WeakHessianTensorSymmetry

open MeasureTheory Set Filter Matrix
open scoped BigOperators ContDiff Topology NNReal ENNReal Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- Literal weak moment transport gives the actual localized trace balance.
The matrix evolution is tested with its genuine bounded compact H1 sandwich,
all finite pairings are integrable, and the boundary pairing is derived.
No classical source Hessian or global trace-energy premise is supplied. -/
theorem weak_moment_localized_raw_trace_balance
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
    (B : Matrix (Fin n) (Fin n) ℝ)
    {χ : Space n → ℝ} (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ) :
    Integrable (fun x => ∑ i, ∑ j, (coordinateHessian u x)⁻¹ i j *
      (2 * (B * coordinateHessian u x * B * T x i).trace) * coordinateDerivative χ j x)
      (potentialMeasure u) ∧
    (∫ x, χ x * (rawHessianTraceGradientTerm (coordinateHessian u x) B (T x) +
      rawHessianTraceTargetTerm (coordinateHessian u x) (coordinateHessian V (gradient u x)) B +
      rawHessianTraceThirdTerm (coordinateHessian u x) B (T x)) ∂potentialMeasure u) =
      (∫ x, χ x * rawHessianTraceSquare (coordinateHessian u x) B ∂potentialMeasure u) -
      (1 / 2 : ℝ) * ∫ x, ∑ i, ∑ j, (coordinateHessian u x)⁻¹ i j *
        (2 * (B * coordinateHessian u x * B * T x i).trace) * coordinateDerivative χ j x
        ∂potentialMeasure u := by
  let Lf (i j a : Fin n) (x : Space n) := ((coordinateHessian u x)⁻¹ * T x i) a j *
    (coordinateDerivative χ a x * (B * coordinateHessian u x * B) i j + χ x * (B * T x a * B) i j)
  let Rf (i j : Fin n) (x : Space n) :=
    (-coordinateHessian u x i j +
      (coordinateHessian u x * coordinateHessian V (gradient u x) * coordinateHessian u x) i j +
      ((coordinateHessian u x)⁻¹ * T x i * (coordinateHessian u x)⁻¹ * T x j).trace) *
      (χ x * (B * coordinateHessian u x * B) i j)
  have hG := weak_moment_gradient_lipschitz_of_uniformlyConvex_target
    hLip hc (hV.of_le (by norm_num)) hVc hκ hstrong hK hKc hpush
  have he (i j : Fin n) :
      (∀ a, Integrable (Lf i j a) (potentialMeasure u)) ∧
      Integrable (Rf i j) (potentialMeasure u) ∧
      -(∑ a, ∫ x, Lf i j a x ∂potentialMeasure u) = ∫ x, Rf i j x ∂potentialMeasure u := by
    obtain ⟨htc,⟨C,hC⟩,htl,hdtl,hdtw⟩ :=
      actual_hessian_sandwich_compact_H1_test hG hTl hTw hχ hχc B i j
    exact weak_moment_hessian_evolution_bounded_H1 hLip hc hV hVc hκ hstrong hK hKc hpush
      hTl hTw htl htc (Eventually.of_forall hC) hdtl hdtw i j
  obtain ⟨hAl,hFl,hDl⟩ :=
    weak_moment_rawTrace_locallyIntegrable hLip hc hV hVc hκ hstrong hK hKc hpush hTl B
  have hAi := integrable_compact_mul_potential_of_locallyIntegrable hLip.continuous hAl hχ.continuous hχc
  have hFi := integrable_compact_mul_potential_of_locallyIntegrable hLip.continuous hFl hχ.continuous hχc
  have hDi := integrable_compact_mul_potential_of_locallyIntegrable hLip.continuous hDl hχ.continuous hχc
  have hSi : Integrable (fun x => χ x * rawHessianTraceSquare (coordinateHessian u x) B)
      (potentialMeasure u) := by
    have hS := (rawHessianTraceSquare_memLp_top
      (memLp_coordinateHessian_top_of_gradient_lipschitz hG (potentialMeasure u)) B).integrable (by simp)
    obtain ⟨C,hC⟩ := hχ.continuous.bounded_above_of_compact_support hχc
    exact hS.bdd_mul hχ.continuous.aestronglyMeasurable (Eventually.of_forall hC)
  have hAe := weak_moment_ae_hessian_equation_of_gradient_lipschitz hLip hc hV.continuous hK hKc hpush hG
  have hTs := actual_weak_third_tensor_ae_symmetric hLip.locallyLipschitz hG.locallyLipschitz hTl hTw
  have hac : potentialMeasure u ≪ volume := withDensity_absolutelyContinuous _ _
  have hleft : ∀ᵐ x ∂potentialMeasure u, (∑ i, ∑ j, ∑ a, Lf i j a x) =
      (1 / 2 : ℝ) * (∑ i, ∑ j, (coordinateHessian u x)⁻¹ i j *
        (2 * (B * coordinateHessian u x * B * T x i).trace) * coordinateDerivative χ j x) +
      χ x * rawHessianTraceGradientTerm (coordinateHessian u x) B (T x) := by
    filter_upwards [hAe.filter_mono hac.ae_le,hTs.filter_mono hac.ae_le] with x hx ht
    have hl := raw_weak_hessian_matrixFlux_trace (coordinateHessian u x) B (T x)
      (fun i j k => (ht i j k).1) (fun i j k => (ht i j k).2)
      (χ x) (fun a => coordinateDerivative χ a x)
    have hb := raw_weak_hessian_trace_boundary_half (coordinateHessian u x) B (T x)
      hx.1.posSemidef.inv.isHermitian.isSymm (fun a => coordinateDerivative χ a x)
    exact hl.trans (congrArg (fun t => t + χ x *
      rawHessianTraceGradientTerm (coordinateHessian u x) B (T x)) hb)
  have hright : ∀ᵐ x ∂potentialMeasure u, (∑ i, ∑ j, Rf i j x) =
      -(χ x * rawHessianTraceSquare (coordinateHessian u x) B) +
      χ x * rawHessianTraceTargetTerm (coordinateHessian u x) (coordinateHessian V (gradient u x)) B +
      χ x * rawHessianTraceThirdTerm (coordinateHessian u x) B (T x) := by
    filter_upwards [hAe.filter_mono hac.ae_le,hTs.filter_mono hac.ae_le] with x hx ht
    have hsym (i : Fin n) : (T x i).IsSymm := Matrix.IsSymm.ext fun j k => (ht i j k).2.symm
    have hr := raw_weak_hessian_trace_right hx.1
      (coordinateHessian_posSemidef_of_convex hV hVc (gradient u x)) B (T x) hsym
    calc
      _ = χ x * (∑ i, ∑ j, (B * coordinateHessian u x * B) i j *
          (-coordinateHessian u x i j +
            (coordinateHessian u x * coordinateHessian V (gradient u x) * coordinateHessian u x) i j +
            ((coordinateHessian u x)⁻¹ * T x i * (coordinateHessian u x)⁻¹ * T x j).trace)) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        dsimp only [Rf]
        ring
      _ = _ := by rw [hr]; ring
  have hbal := integral_balance_of_finite_component_evolution
    (fun i j a => (he i j).1 a) (fun i j => (he i j).2.1)
    hSi hAi hFi hDi hleft hright (fun i j => (he i j).2.2)
  refine ⟨hbal.1, ?_⟩
  calc
    _ = ∫ x, χ x * rawHessianTraceGradientTerm (coordinateHessian u x) B (T x) +
      χ x * rawHessianTraceTargetTerm (coordinateHessian u x) (coordinateHessian V (gradient u x)) B +
      χ x * rawHessianTraceThirdTerm (coordinateHessian u x) B (T x) ∂potentialMeasure u := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by ring
    _ = _ := hbal.2

end KLS
end

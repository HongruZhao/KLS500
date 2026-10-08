import KLS.WeakEllipticCompactTransfer

open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped Topology ContDiff NNReal ENNReal Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- The actual density-weighted elliptic expression is exactly the genuine
 inverse-Hessian diffusion; this is an algebraic identity. -/
theorem weakEllipticExpression_weighted_inverseHessian
    (u V f : Space n → ℝ) (x : Space n) :
    weakEllipticExpression (fun y => Real.exp (-u y) • (coordinateHessian u y)⁻¹)
      (fun j y => Real.exp (-u y)*coordinateDerivative V j (gradient u y)) f x =
      Real.exp (-u x)*hessianMetricDiffusion u V f x := by
  simp only [weakEllipticExpression,hessianMetricDiffusion,Matrix.smul_apply,
    smul_eq_mul,mul_sub,Finset.mul_sum,mul_assoc]

/-- Compact self-adjoint transfer for the actual weak moment potential and
 an actual C1 scalar function with Lipschitz gradient. Every integrability
 conclusion is derived from compact support and actual weak transport. -/
theorem weak_moment_hessianMetricDiffusion_compact_transfer
    {u V f η : Space n → ℝ} {L G : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : ContDiff ℝ 1 V) (hVc : ConvexOn ℝ univ V)
    {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun p => V p - (κ / 2) * ‖p‖ ^ 2))
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    (hf : ContDiff ℝ 1 f) (hGf : LipschitzWith G (gradient f))
    (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) :
    Integrable (fun x => η x*hessianMetricDiffusion u V f x) (potentialMeasure u) ∧
    Integrable (fun x => f x*hessianMetricDiffusion u V η x) (potentialMeasure u) ∧
    (∫ x, η x*hessianMetricDiffusion u V f x ∂potentialMeasure u) =
      ∫ x, f x*hessianMetricDiffusion u V η x ∂potentialMeasure u := by
  have hG := weak_moment_gradient_lipschitz_of_uniformlyConvex_target
    hLip hc hV hVc hκ hstrong hK hKc hpush
  have hAe := weak_moment_ae_hessian_equation_of_gradient_lipschitz hLip hc hV.continuous hK hKc hpush hG
  let A : Space n → Matrix (Fin n) (Fin n) ℝ := fun x => Real.exp (-u x) • (coordinateHessian u x)⁻¹
  let b : Fin n → Space n → ℝ := fun j x => Real.exp (-u x)*coordinateDerivative V j (gradient u x)
  have hA (i j : Fin n) (S : Set (Space n)) (hS : IsCompact S) :
      MemLp (fun x => A x i j) 2 (volume.restrict S) :=
    memLp_weighted_inverseHessian_on_compact_of_ae_equation hLip hG hV.continuous
      (hAe.mono (fun _ hx => ⟨hx.1,hx.2.1⟩)) hS i j
  have hb (j : Fin n) (S : Set (Space n)) (hS : IsCompact S) :
      MemLp (b j) 2 (volume.restrict S) :=
    memLp_continuous_on_compact
      ((Real.continuous_exp.comp hLip.continuous.neg).mul
        (((contDiff_coordinateDerivative hV (m := 0) (by norm_num) j).continuous).comp hG.continuous)) hS
  have hsymm : ∀ᵐ x ∂(volume : Measure (Space n)), (A x).IsSymm := by
    filter_upwards [hAe] with x hx
    exact hx.1.isHermitian.isSymm.inv.smul _
  have hdiv (j : Fin n) (ψ : Space n → ℝ) (hψ : LocallyLipschitz ψ) (hψc : HasCompactSupport ψ) :
      (∑ i, ∫ x, A x i j*coordinateDerivative ψ i x) = ∫ x, b j x*ψ x :=
    weak_moment_inverseHessian_integral_column_locallyLipschitz_volume
      hLip hc hV hVc hκ hstrong hK hKc hpush hψ hψc j
  obtain ⟨hleft,hright,heq⟩ := integral_weakEllipticExpression_compact_transfer hA hb hsymm hdiv hf hGf hη hηc
  have hop (g : Space n → ℝ) (x : Space n) :
      weakEllipticExpression A b g x = Real.exp (-u x)*hessianMetricDiffusion u V g x :=
    weakEllipticExpression_weighted_inverseHessian u V g x
  refine ⟨(integrable_potentialMeasure_iff hLip.continuous.measurable).mpr ?_,
    (integrable_potentialMeasure_iff hLip.continuous.measurable).mpr ?_,?_⟩
  · simpa only [hop,mul_comm,mul_left_comm,mul_assoc] using hleft
  · simpa only [hop,mul_comm,mul_left_comm,mul_assoc] using hright
  · simpa only [integral_potentialMeasure hLip.continuous.measurable,hop,mul_comm,mul_left_comm,mul_assoc] using heq

end KLS
end

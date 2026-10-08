import KLS.AdjugateExponentialGradientCalculus

open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped Topology ContDiff NNReal ENNReal Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- The actual bounded adjugate Hessian pairs integrably with every compact
 continuous function. -/
theorem integrable_adjugateHessian_mul_continuous_compact
    {u ψ : Space n → ℝ} {L G : ℝ≥0} (hLip : LipschitzWith L u)
    (hG : LipschitzWith G (gradient u)) (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (i j : Fin n) : Integrable (fun x => (coordinateHessian u x).adjugate i j*ψ x) := by
  obtain ⟨C,hC,hbound,_⟩ := exists_uniform_adjugate_bound_of_gradient_lipschitz hLip hG
  have hmat : Measurable (fun x : Space n => (coordinateHessian u x).adjugate) :=
    (show Continuous (fun A : Matrix (Fin n) (Fin n) ℝ => A.adjugate) from
      MatrixCalculus.contDiff_adjugate.continuous).measurable.comp (measurable_coordinateHessian u)
  exact (hψ.integrable_of_hasCompactSupport hc).bdd_mul
    ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hmat)).aestronglyMeasurable
    (Eventually.of_forall fun x => (Matrix.norm_le_iff hC).mp (hbound x) i j)

/-- The actual inverse Hessian of a weak moment potential satisfies weighted
 divergence against compact C1 tests. No continuous second derivatives or
 derivative of the Hessian is assumed. -/
theorem weak_moment_inverseHessian_integral_column_volume
    {u V ψ : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : ContDiff ℝ 1 V) (hVc : ConvexOn ℝ univ V)
    {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun p => V p - (κ / 2) * ‖p‖ ^ 2))
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) (j : Fin n) :
    (∑ i, ∫ x, Real.exp (-u x)*(coordinateHessian u x)⁻¹ i j*coordinateDerivative ψ i x) =
      ∫ x, Real.exp (-u x)*coordinateDerivative V j (gradient u x)*ψ x := by
  have hG := weak_moment_gradient_lipschitz_of_uniformlyConvex_target
    hLip hc hV hVc hκ hstrong hK hKc hpush
  let χ : Space n → ℝ := fun x => ψ x*Real.exp (-V (gradient u x))
  have hχ : LocallyLipschitz χ := locallyLipschitz_mul_exp_neg_comp_gradient hG hV hψ.locallyLipschitz
  have hχc : HasCompactSupport χ := hψc.mul_right
  have hzero := weak_moment_adjugateHessian_integral_column_locallyLipschitz
    hLip hc hV hVc hκ hstrong hK hKc hpush hχ hχc j
  have hAe := weak_moment_ae_hessian_equation_of_gradient_lipschitz hLip hc hV.continuous hK hKc hpush hG
  have hAint (i : Fin n) : Integrable
      (fun x => (coordinateHessian u x).adjugate i j*coordinateDerivative χ i x) :=
    integrable_mul_coordinateDerivative_of_localL2 hχ hχc
      (fun S hS => memLp_adjugateHessian_on_compact_of_gradient_lipschitz hLip hG hS i j) i
  have hflux (i : Fin n) : Integrable
      (fun x => Real.exp (-V (gradient u x))*(coordinateHessian u x).adjugate i j*coordinateDerivative ψ i x) := by
    have hd := (contDiff_coordinateDerivative hψ (m := 0) (by norm_num) i).continuous
    have ht := integrable_adjugateHessian_mul_continuous_compact hLip hG
      ((Real.continuous_exp.comp (hV.continuous.comp hG.continuous).neg).mul hd)
      ((hasCompactSupport_coordinateDerivative hψc i).mul_left) i j
    convert ht using 1
    funext x
    dsimp only [Function.comp_def,Pi.mul_apply,Pi.neg_apply]
    ring
  have hrhs : Integrable
      (fun x => Real.exp (-u x)*coordinateDerivative V j (gradient u x)*ψ x) :=
    (((Real.continuous_exp.comp hLip.continuous.neg).mul
      (((contDiff_coordinateDerivative hV (m := 0) (by norm_num) j).continuous).comp hG.continuous)).mul
      hψ.continuous).integrable_of_hasCompactSupport hψc.mul_left
  have hid : (∫ x, ∑ i, (coordinateHessian u x).adjugate i j*coordinateDerivative χ i x) =
      (∫ x, (∑ i, Real.exp (-V (gradient u x))*(coordinateHessian u x).adjugate i j*
        coordinateDerivative ψ i x) - Real.exp (-u x)*coordinateDerivative V j (gradient u x)*ψ x) := by
    apply integral_congr_ae
    filter_upwards [hAe] with x hx
    exact adjugate_exp_neg_gradient_test_identity ((hV.differentiable (by norm_num)) _)
      ((hψ.differentiable (by norm_num)) x) hx.2.2.1.differentiableAt hx.1 hx.2.1 j
  rw [integral_finsetSum _ (fun i _ => hAint i),hzero,
    integral_sub (integrable_finsetSum _ (fun i _ => hflux i)) hrhs,
    integral_finsetSum _ (fun i _ => hflux i)] at hid
  have he (i : Fin n) : (∫ x, Real.exp (-V (gradient u x))*(coordinateHessian u x).adjugate i j*
      coordinateDerivative ψ i x) =
      ∫ x, Real.exp (-u x)*(coordinateHessian u x)⁻¹ i j*coordinateDerivative ψ i x := by
    apply integral_congr_ae
    filter_upwards [hAe] with x hx
    rw [exp_neg_target_mul_adjugate_eq_exp_neg_source_mul_inverse hx.1 hx.2.1]
  simp_rw [he] at hid
  linarith

/-- In the actual source potential measure, the weak inverse Hessian has
 precisely the target-gradient drift. -/
theorem weak_moment_inverseHessian_integral_column
    {u V ψ : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : ContDiff ℝ 1 V) (hVc : ConvexOn ℝ univ V)
    {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun p => V p - (κ / 2) * ‖p‖ ^ 2))
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) (j : Fin n) :
    (∑ i, ∫ x, (coordinateHessian u x)⁻¹ i j*coordinateDerivative ψ i x ∂potentialMeasure u) =
      ∫ x, coordinateDerivative V j (gradient u x)*ψ x ∂potentialMeasure u := by
  simpa only [integral_potentialMeasure hLip.continuous.measurable,mul_comm,mul_left_comm,mul_assoc] using
    weak_moment_inverseHessian_integral_column_volume hLip hc hV hVc hκ hstrong hK hKc hpush hψ hψc j

end KLS
end

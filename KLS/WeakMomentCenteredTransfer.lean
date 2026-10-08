import KLS.C11CenteredDifferenceCalculus

open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped Topology ContDiff NNReal ENNReal Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- The genuine weak inverse-Hessian diffusion of a compact C2 test is L1;
 its coefficient regularity and integrability are derived from weak transport. -/
theorem weak_moment_integrable_diffusion_compact_test
    {u V η : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : ContDiff ℝ 1 V) (hVc : ConvexOn ℝ univ V)
    {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun p => V p - (κ / 2) * ‖p‖ ^ 2))
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) :
    Integrable (hessianMetricDiffusion u V η) (potentialMeasure u) := by
  have hG : LipschitzWith 0 (gradient (fun _ : Space n => (1 : ℝ))) := by
    simp only [gradient_fun_const']
    exact LipschitzWith.of_dist_le_mul (fun _ _ => by simp)
  have hh := weak_moment_hessianMetricDiffusion_compact_transfer
    hLip hc hV hVc hκ hstrong hK hKc hpush contDiff_const hG hη hηc
  simpa only [one_mul] using hh.2.1

/-- The actual centered increment admits compact self-adjoint transfer with
 every compact C2 test, without source Hessian derivatives. -/
theorem weak_moment_centered_difference_compact_transfer
    {u V η : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : ContDiff ℝ 1 V) (hVc : ConvexOn ℝ univ V)
    {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun p => V p - (κ / 2) * ‖p‖ ^ 2))
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) (h : Space n) :
    Integrable (fun x => η x*hessianMetricDiffusion u V (symmetricSecondDifference u h) x) (potentialMeasure u) ∧
    Integrable (fun x => symmetricSecondDifference u h x*hessianMetricDiffusion u V η x) (potentialMeasure u) ∧
    (∫ x, η x*hessianMetricDiffusion u V (symmetricSecondDifference u h) x ∂potentialMeasure u) =
      ∫ x, symmetricSecondDifference u h x*hessianMetricDiffusion u V η x ∂potentialMeasure u := by
  have hu := moment_contDiff_one_closedTarget hLip hc hV.continuous hK hKc hpush
  have hG := weak_moment_gradient_lipschitz_of_uniformlyConvex_target hLip hc hV hVc hκ hstrong hK hKc hpush
  exact weak_moment_hessianMetricDiffusion_compact_transfer hLip hc hV hVc hκ hstrong hK hKc hpush
    (symmetricSecondDifference_contDiff hu h)
    (lipschitz_gradient_symmetricSecondDifference (hu.differentiable (by norm_num)) hG h) hη hηc

/-- A genuine O(norm h squared) compact bound obtained by moving the weak
 operator off the actual centered increment. No Hessian energy is assumed. -/
theorem weak_moment_centered_difference_compact_integral_bound
    {u V η : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : ContDiff ℝ 1 V) (hVc : ConvexOn ℝ univ V)
    {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun p => V p - (κ / 2) * ‖p‖ ^ 2))
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) (h : Space n) :
    Integrable (fun x => η x*(hessianMetricDiffusion u V (symmetricSecondDifference u h) x+
      symmetricSecondDifference u h x)) (potentialMeasure u) ∧
    (∫ x, η x*(hessianMetricDiffusion u V (symmetricSecondDifference u h) x+
      symmetricSecondDifference u h x) ∂potentialMeasure u) ≤
      (4/κ)*‖h‖^2 * ∫ x, ‖η x+hessianMetricDiffusion u V η x‖ ∂potentialMeasure u := by
  let δ := symmetricSecondDifference u h
  have hu := moment_contDiff_one_closedTarget hLip hc hV.continuous hK hKc hpush
  have hδ : Continuous δ := (symmetricSecondDifference_contDiff hu h).continuous
  obtain ⟨hleft,hright,heq⟩ := weak_moment_centered_difference_compact_transfer
    hLip hc hV hVc hκ hstrong hK hKc hpush hη hηc h
  have hηδ : Integrable (fun x => η x*δ x) (potentialMeasure u) :=
    integrable_potentialMeasure_of_continuous_hasCompactSupport hLip.continuous (hη.continuous.mul hδ) hηc.mul_right
  have hδη : Integrable (fun x => δ x*η x) (potentialMeasure u) := by simpa only [mul_comm] using hηδ
  have hl : Integrable (fun x => η x*(hessianMetricDiffusion u V δ x+δ x)) (potentialMeasure u) := by
    convert hleft.add hηδ using 1
    funext x
    dsimp only [Pi.add_apply,δ]
    ring
  have hr : Integrable (fun x => δ x*(η x+hessianMetricDiffusion u V η x)) (potentialMeasure u) := by
    convert hδη.add hright using 1
    funext x
    dsimp only [Pi.add_apply,δ]
    ring
  have hi : (∫ x, η x*(hessianMetricDiffusion u V δ x+δ x) ∂potentialMeasure u) =
      ∫ x, δ x*(η x+hessianMetricDiffusion u V η x) ∂potentialMeasure u := by
    simp_rw [mul_add]
    rw [integral_add hleft hηδ,integral_add hδη hright,heq]
    have hcomm : (∫ x, η x*δ x ∂potentialMeasure u) = ∫ x, δ x*η x ∂potentialMeasure u := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun _ => mul_comm _ _)
    rw [hcomm]
    ring
  have hLη := weak_moment_integrable_diffusion_compact_test hLip hc hV hVc hκ hstrong hK hKc hpush hη hηc
  have hηint := integrable_potentialMeasure_of_continuous_hasCompactSupport hLip.continuous hη.continuous hηc
  have hmajor : Integrable (fun x => ((4/κ)*‖h‖^2)*‖η x+hessianMetricDiffusion u V η x‖) (potentialMeasure u) :=
    (hηint.add hLη).norm.const_mul _
  have hb (x : Space n) : δ x*(η x+hessianMetricDiffusion u V η x) ≤
      ((4/κ)*‖h‖^2)*‖η x+hessianMetricDiffusion u V η x‖ := by
    have hδ0 := symmetricSecondDifference_nonneg hc h x
    have hδB : δ x ≤ (4/κ)*‖h‖^2 := by
      convert weak_moment_symmetricSecondDifference_le_of_uniformlyConvex_target
        hLip hc hV hVc hκ hstrong hK hKc hpush h x using 1
      ring
    have he : η x+hessianMetricDiffusion u V η x ≤ ‖η x+hessianMetricDiffusion u V η x‖ := by
      simpa only [Real.norm_eq_abs] using le_abs_self (η x+hessianMetricDiffusion u V η x)
    exact (mul_le_mul_of_nonneg_left he hδ0).trans
      (mul_le_mul_of_nonneg_right hδB (norm_nonneg _))
  refine ⟨hl,?_⟩
  change (∫ x, η x*(hessianMetricDiffusion u V δ x+δ x) ∂potentialMeasure u) ≤ _
  rw [hi]
  exact (integral_mono hr hmajor hb).trans_eq (integral_const_mul _ _)

end KLS
end

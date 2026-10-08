import KLS.WeakMomentCenteredCoercivity

open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped Topology ContDiff NNReal ENNReal Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- Every translated actual Hessian entry is L2 in every finite measure,
 using the genuine global gradient Lipschitz bound and actual measurability. -/
theorem memLp_translated_coordinateHessian_of_gradient_lipschitz
    {u : Space n → ℝ} {G : ℝ≥0} (hG : LipschitzWith G (gradient u))
    (μ : Measure (Space n)) [IsFiniteMeasure μ] (h : Space n) (i j : Fin n) :
    MemLp (fun x => coordinateHessian u (x+h) i j) 2 μ := by
  have hm := ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp
    (measurable_coordinateHessian u))).comp (measurable_id.add_const h)
  apply MemLp.of_bound hm.aestronglyMeasurable (G : ℝ)
  exact Eventually.of_forall (fun x => coordinateHessian_entry_bound_of_gradient_lipschitz hG (x+h) i j)

/-- Squared actual Hessian increments are integrable in every finite measure. -/
theorem integrable_frobenius_coordinateHessian_increment
    {u : Space n → ℝ} {G : ℝ≥0} (hG : LipschitzWith G (gradient u))
    (μ : Measure (Space n)) [IsFiniteMeasure μ] (h : Space n) :
    Integrable (fun x => matrixFrobeniusSq (coordinateHessian u (x+h)-coordinateHessian u x)) μ := by
  unfold matrixFrobeniusSq
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  simpa only [add_zero,Pi.sub_apply,Matrix.sub_apply] using
    ((memLp_translated_coordinateHessian_of_gradient_lipschitz hG μ h i j).sub
      (memLp_translated_coordinateHessian_of_gradient_lipschitz hG μ 0 i j)).integrable_sq

/-- Nonnegative compact C2 tests yield a genuine O(norm h squared) bound
 for both actual squared Hessian increments, directly from weak transport. -/
theorem weak_moment_compact_hessian_increment_energy_bound
    {u V η : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : ContDiff ℝ 1 V) (hVc : ConvexOn ℝ univ V)
    {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun p => V p - (κ / 2) * ‖p‖ ^ 2))
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) (hη0 : ∀ x, 0 ≤ η x) (h : Space n) :
    (((16/κ)⁻¹)^2/2) *
      (∫ x, η x*(matrixFrobeniusSq (coordinateHessian u (x+h)-coordinateHessian u x) +
        matrixFrobeniusSq (coordinateHessian u (x-h)-coordinateHessian u x)) ∂potentialMeasure u) ≤
      (4/κ)*‖h‖^2 * ∫ x, ‖η x+hessianMetricDiffusion u V η x‖ ∂potentialMeasure u := by
  have hG := weak_moment_gradient_lipschitz_of_uniformlyConvex_target hLip hc hV hVc hκ hstrong hK hKc hpush
  have hp := integrable_frobenius_coordinateHessian_increment hG (potentialMeasure u) h
  have hm : Integrable (fun x => matrixFrobeniusSq (coordinateHessian u (x-h)-coordinateHessian u x))
      (potentialMeasure u) := by
    simpa only [sub_eq_add_neg] using integrable_frobenius_coordinateHessian_increment hG (potentialMeasure u) (-h)
  obtain ⟨C,hC⟩ := hηc.exists_bound_of_continuous hη.continuous
  have he := (hp.add hm).bdd_mul hη.continuous.aestronglyMeasurable (Eventually.of_forall hC)
  obtain ⟨hr,hbound⟩ := weak_moment_centered_difference_compact_integral_bound
    hLip hc hV hVc hκ hstrong hK hKc hpush hη hηc h
  have hgap := weak_moment_centered_difference_coercivity_ae hLip hc hV hVc hκ hstrong hK hKc hpush h
  have hρ : potentialMeasure u ≪ volume := withDensity_absolutelyContinuous _ _
  have hi := integral_mono_ae (he.const_mul (((16/κ)⁻¹)^2/2)) hr (by
    filter_upwards [hρ.ae_le hgap] with x hx
    change (((16/κ)⁻¹)^2/2) *
      (η x*(matrixFrobeniusSq (coordinateHessian u (x+h)-coordinateHessian u x) +
        matrixFrobeniusSq (coordinateHessian u (x-h)-coordinateHessian u x))) ≤ _
    convert mul_le_mul_of_nonneg_left hx (hη0 x) using 1
    ring)
  rw [integral_const_mul] at hi
  exact hi.trans hbound

/-- A fixed nonnegative compact smooth test gives one finite uniform
 constant for all actual Hessian increments. -/
theorem weak_moment_exists_compact_hessian_increment_bound
    {u V η : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : ContDiff ℝ 1 V) (hVc : ConvexOn ℝ univ V)
    {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun p => V p - (κ / 2) * ‖p‖ ^ 2))
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) (hη0 : ∀ x, 0 ≤ η x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : Space n,
      (∫ x, η x*(matrixFrobeniusSq (coordinateHessian u (x+h)-coordinateHessian u x) +
        matrixFrobeniusSq (coordinateHessian u (x-h)-coordinateHessian u x)) ∂potentialMeasure u) ≤ C*‖h‖^2 := by
  let c : ℝ := ((16/κ)⁻¹)^2/2
  let D : ℝ := ∫ x, ‖η x+hessianMetricDiffusion u V η x‖ ∂potentialMeasure u
  have hcpos : 0 < c := by dsimp [c]; positivity
  have hD : 0 ≤ D := integral_nonneg (fun _ => norm_nonneg _)
  refine ⟨((4/κ)*D)/c,by positivity,?_⟩
  intro h
  have hb := weak_moment_compact_hessian_increment_energy_bound
    hLip hc hV hVc hκ hstrong hK hKc hpush hη hηc hη0 h
  have hi : (∫ x, η x*(matrixFrobeniusSq (coordinateHessian u (x+h)-coordinateHessian u x) +
      matrixFrobeniusSq (coordinateHessian u (x-h)-coordinateHessian u x)) ∂potentialMeasure u) ≤
      ((4/κ)*‖h‖^2*D)/c := by
    apply (le_div_iff₀ hcpos).mpr
    simpa only [c,D,mul_comm] using hb
  convert hi using 1
  ring

end KLS
end

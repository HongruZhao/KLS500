import KLS.WeakMomentLocalDifferenceEnergy

open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped Topology ContDiff NNReal ENNReal Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- Each actual Hessian entry has one uniform cutoff-weighted volume L2
 increment bound. The cutoff is any genuine continuous compact function;
 no weak derivative or Hessian energy premise occurs. -/
theorem weak_moment_cutoff_hessian_increment_bound
    {u V χ : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : ContDiff ℝ 1 V) (hVc : ConvexOn ℝ univ V)
    {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun p => V p - (κ / 2) * ‖p‖ ^ 2))
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ h : Space n, ∀ i j : Fin n,
      Integrable (fun x => (χ x)^2*(coordinateHessian u (x+h) i j-coordinateHessian u x i j)^2) ∧
      (∫ x, (χ x)^2*(coordinateHessian u (x+h) i j-coordinateHessian u x i j)^2) ≤ M*‖h‖^2 := by
  let S := tsupport χ
  have hS : IsCompact S := hχc
  have : IsFiniteMeasure (volume.restrict S) := ⟨by simpa using hS.measure_lt_top⟩
  obtain ⟨C,hC,hCbound⟩ := weak_moment_local_hessian_increment_bound
    hLip hc hV hVc hκ hstrong hK hKc hpush hS
  obtain ⟨B,hB⟩ := hχc.exists_bound_of_continuous hχ
  have hG := weak_moment_gradient_lipschitz_of_uniformlyConvex_target hLip hc hV hVc hκ hstrong hK hKc hpush
  refine ⟨B^2*C,mul_nonneg (sq_nonneg B) hC,?_⟩
  intro h i j
  let E : Space n → ℝ := fun x => (coordinateHessian u (x+h) i j-coordinateHessian u x i j)^2
  have hEi : Integrable E (volume.restrict S) := by
    simpa only [add_zero,Pi.sub_apply] using
      ((memLp_translated_coordinateHessian_of_gradient_lipschitz hG (volume.restrict S) h i j).sub
        (memLp_translated_coordinateHessian_of_gradient_lipschitz hG (volume.restrict S) 0 i j)).integrable_sq
  have hEI : Integrable (S.indicator E) := (integrable_indicator_iff hS.measurableSet).mpr hEi
  have hmajor : Integrable (fun x => B^2*S.indicator E x) := hEI.const_mul _
  have hentry : Measurable (fun x => coordinateHessian u x i j) :=
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp (measurable_coordinateHessian u))
  have hm : Measurable (fun x => (χ x)^2*E x) :=
    (hχ.measurable.pow_const 2).mul (((hentry.comp (measurable_id.add_const h)).sub hentry).pow_const 2)
  have hb (x : Space n) : (χ x)^2*E x ≤ B^2*S.indicator E x := by
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx]
      have hsq : (χ x)^2 ≤ B^2 := by
        simpa only [Real.norm_eq_abs,sq_abs] using pow_le_pow_left₀ (norm_nonneg (χ x)) (hB x) 2
      exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    · have hχ0 : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
      rw [indicator_of_notMem hx,hχ0]
      simp
  have hminor : Integrable (fun x => (χ x)^2*E x) := by
    apply hmajor.mono' hm.aestronglyMeasurable
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      exact hb x
  have hi := integral_mono hminor hmajor hb
  rw [integral_const_mul,integral_indicator hS.measurableSet] at hi
  have hh := hi.trans (mul_le_mul_of_nonneg_left (hCbound h i j) (sq_nonneg B))
  exact ⟨hminor,by simpa only [E,mul_assoc] using hh⟩

end KLS
end

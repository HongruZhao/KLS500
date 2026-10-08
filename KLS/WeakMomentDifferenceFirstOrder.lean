import KLS.MomentPrimalC1
import KLS.MomentMapUniformHessianBound

open MeasureTheory Set Filter InnerProductSpace
open scoped Topology ContDiff NNReal
noncomputable section
namespace KLS
variable {n : ℕ}

/-- The actual weak moment transport has bounded gradient, derived from its
Lipschitz bound and the already-proved C1 theorem. -/
theorem bounded_gradient_of_weak_moment_transport
    {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : Continuous V)
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K) :
    Bornology.IsBounded (range (gradient u)) := by
  have hd := (moment_contDiff_one_closedTarget hLip hc hV hK hKc hpush).differentiable
    (by norm_num)
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨L,?_⟩
  rintro _ ⟨x,rfl⟩
  exact norm_le_of_mem_convexSubgradient hLip (gradient_mem_convexSubgradient hc (hd x))

/-- All first-order finite-difference maximum estimates hold for the original
weak moment potential. Its C1 regularity and actual maximum are derived. The
missing second-order comparison is not included in the conclusion. -/
theorem exists_weak_moment_penalized_maximum_first_order
    {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : ContDiff ℝ 1 V) (hVc : ConvexOn ℝ univ V)
    {κ : ℝ} (hstrong : ConvexOn ℝ univ (fun p => V p - (κ / 2) * ‖p‖ ^ 2))
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : Space n, ∀ η : ℝ, 0 < η →
      ∃ x : Space n,
        (∀ y, symmetricSecondDifference u h y - η * u y ≤
          symmetricSecondDifference u h x - η * u x) ∧
        gradient u (x + h) + gradient u (x - h) - (2 : ℝ) • gradient u x =
          η • gradient u x ∧
        symmetricSecondDifference u h x ≤
          2 * ‖h‖ * ‖(1 / 2 : ℝ) • (gradient u (x + h) - gradient u (x - h))‖ ∧
        κ * ‖(1 / 2 : ℝ) • (gradient u (x + h) - gradient u (x - h))‖ ^ 2 ≤
          symmetricSecondDifference (fun z => V (gradient u z)) h x + η * C := by
  have hd := (moment_contDiff_one_closedTarget hLip hc hV.continuous hK hKc hpush).differentiable
    (by norm_num)
  obtain ⟨C,hC,hbound⟩ := exists_bound_radial_target_derivative hV
    (bounded_gradient_of_weak_moment_transport hLip hc hV.continuous hK hKc hpush)
  refine ⟨C,hC,?_⟩
  intro h η hη
  obtain ⟨x,hmax⟩ := exists_maximizer_penalizedSecondDifference hLip.continuous hc hLip h hη
  refine ⟨x,hmax,gradient_symmetricSecondDifference_at_penalized_max hd h η x hmax,?_,?_⟩
  · have hh := (symmetricSecondDifference_le_gradient_difference hc hd h x).trans
      ((le_abs_self _).trans (abs_real_inner_le_norm _ _))
    have heq : ‖(1 / 2 : ℝ) • (gradient u (x + h) - gradient u (x - h))‖ =
        (1 / 2 : ℝ) * ‖gradient u (x + h) - gradient u (x - h)‖ := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0 : ℝ) < 1/2)]
    rw [heq]
    nlinarith
  · have hlo := target_gap_lower_at_penalized_max hd (hV.differentiable (by norm_num))
      hVc hstrong h η x hmax
    have hb := (neg_abs_le (fderiv ℝ V (gradient u x) (gradient u x))).trans'
      (neg_le_neg (hbound x))
    have hb' := mul_le_mul_of_nonneg_left hb hη.le
    linarith

end KLS
end

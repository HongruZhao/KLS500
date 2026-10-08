import KLS.DyadicSubgradientModulus
import KLS.UniformSectionLocalization

/-! A genuine quantitative interior gradient modulus for the weak moment
potential. All section-localization and opposite-deficit hypotheses are
discharged from its actual transport equation and the established C1 theorem.
The geometric decay rate is constructed, not assumed. -/

open MeasureTheory InnerProductSpace Set Filter Metric
open scoped Topology NNReal ENNReal

noncomputable section
namespace KLS

variable {n : ℕ}

theorem exists_local_moment_supportDeficit_comparison
    (hn : 0 < n) {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : Continuous V)
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    (c : Space n) :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧
      ∀ x ∈ closedBall c r, ∀ y ∈ closedBall c r,
        ∀ p ∈ convexSubgradient u x, ∀ q ∈ convexSubgradient u y,
          supportDeficit u x p y ≤ C * supportDeficit u y q x := by
  obtain ⟨r₀, t, hr₀, ht, hsmall⟩ :=
    exists_uniform_small_moment_sections hLip hc hV hK hKc hpush c (by norm_num : (0 : ℝ) < 1)
  let r : ℝ := min r₀ (t / (8 * ((L : ℝ) + 1)))
  have hr : 0 < r := lt_min hr₀ (by positivity)
  have hrr : r ≤ r₀ := min_le_left _ _
  have hscale : 8 * (L : ℝ) * r ≤ t := by
    have hh : r ≤ t / (8 * ((L : ℝ) + 1)) := min_le_right _ _
    have hmul := (le_div_iff₀ (by positivity : 0 < 8 * ((L : ℝ) + 1))).mp hh
    nlinarith
  have hd := (moment_contDiff_one_closedTarget hLip hc hV hK hKc hpush).differentiable (by norm_num)
  have hsmall' : ∀ x ∈ closedBall c r, ∀ p ∈ convexSubgradient u x,
      ∀ h : ℝ, 0 < h → h ≤ t → closedCenteredSection u x p h ⊆ closedBall c 1 := by
    intro x hx p hp h _ hh
    have heq := eq_gradient_of_mem_convexSubgradient (hd x) hp
    rw [heq]
    exact (hsmall x (closedBall_subset_closedBall hrr hx) h hh).trans ball_subset_closedBall
  obtain ⟨C, hC, hcomp⟩ := exists_uniform_moment_deficit_comparison_of_small_sections
    hn hLip hc hV hK.measurableSet hKc hpush (isCompact_closedBall c 1) hscale hsmall'
  exact ⟨r, C, hr, hC, hcomp⟩

/-- At every source point the actual gradient has a uniform geometric modulus
on a neighborhood. For all k, distances at most r·2^{-(k+1)} force gradient
differences at most 4L·q^k, with a constructed 0<q<1. -/
theorem exists_local_moment_gradient_dyadic_modulus
    (hn : 0 < n) {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : Continuous V)
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    (c : Space n) :
    ∃ r q : ℝ, 0 < r ∧ 0 < q ∧ q < 1 ∧
      ∀ x ∈ closedBall c r, ∀ k : ℕ, ∀ y : Space n,
        ‖y - x‖ ≤ r * (1 / 2 : ℝ) ^ (k + 1) →
          ‖gradient u y - gradient u x‖ ≤ 4 * (L : ℝ) * q ^ k := by
  obtain ⟨r₀, C, hr₀, hC, hcomp⟩ :=
    exists_local_moment_supportDeficit_comparison hn hLip hc hV hK hKc hpush c
  have hq := dyadic_subgradient_decay_factor_lt_one hC
  refine ⟨r₀ / 2, 2 * sectionDeficitContractionFactor C, by positivity, hq.1, hq.2, ?_⟩
  intro x hx k y hy
  have hball : closedBall x (r₀ / 2) ⊆ closedBall c r₀ := by
    intro z hz
    have hxn : ‖x - c‖ ≤ r₀ / 2 := hx
    have hzn : ‖z - x‖ ≤ r₀ / 2 := hz
    change ‖z - c‖ ≤ r₀
    have hh := norm_sub_le_norm_sub_add_norm_sub z x c
    linarith
  have hd := (moment_contDiff_one_closedTarget hLip hc hV hK hKc hpush).differentiable (by norm_num)
  exact norm_subgradient_sub_le_dyadic hLip hc (convex_closedBall c r₀) hC hcomp
    (by positivity : 0 < r₀ / 2) hball
    (gradient_mem_convexSubgradient hc (hd x)) (gradient_mem_convexSubgradient hc (hd y)) k hy

end KLS
end

#print axioms KLS.exists_local_moment_supportDeficit_comparison
#print axioms KLS.exists_local_moment_gradient_dyadic_modulus

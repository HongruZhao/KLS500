import KLS.DyadicToHolder
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz

/-! The actual Alexandrov density is locally Hölder when the finite target
potential is convex. Its local Lipschitz bound is derived from convexity on a
compact gradient ball, and the gradient Hölder exponent is the one constructed
by the section iteration. No Hessian regularity is assumed. -/

open MeasureTheory InnerProductSpace Set Filter Metric
open scoped Topology NNReal ENNReal

noncomputable section
namespace KLS

theorem exists_local_momentMongeAmpereDensity_holder_bound
    {n : ℕ} (hn : 0 < n) {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : Continuous V) (hVc : ConvexOn ℝ univ V)
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    (c : Space n) :
    ∃ r α A : ℝ, 0 < r ∧ 0 < α ∧ α ≤ 1 ∧ 0 < A ∧
      ∀ x ∈ closedBall c r, ∀ y ∈ closedBall c r,
        |(momentMongeAmpereDensity u V y).toReal - (momentMongeAmpereDensity u V x).toReal| ≤
          A * ‖y - x‖ ^ α := by
  obtain ⟨r₀, α, H, hr₀, hα, hα1, hH, hgrad⟩ :=
    exists_local_moment_gradient_holder_bound hn hLip hc hV hK hKc hpush c
  let r : ℝ := min r₀ (1 / 2)
  have hr : 0 < r := lt_min hr₀ (by norm_num)
  have hrr : r ≤ r₀ := min_le_left _ _
  have hrhalf : r ≤ 1 / 2 := min_le_right _ _
  have hgradcont := continuous_gradient_of_subsingleton_convexSubgradient hLip hc
    (moment_convexSubgradient_subsingleton_closedTarget hLip hc hV hK hKc hpush)
  let F : Space n → ℝ := fun x => -u x + V (gradient u x)
  have hF : Continuous F := hLip.continuous.neg.add (hV.comp hgradcont)
  obtain ⟨B, hB⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_closedBall (0 : Space n) (L : ℝ)) hVc.locallyLipschitz.locallyLipschitzOn
  obtain ⟨E, hE⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    ((isCompact_closedBall c r).image hF) convexOn_exp.locallyLipschitz.locallyLipschitzOn
  let A : ℝ := 1 + (E : ℝ) * ((L : ℝ) + (B : ℝ) * H)
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨r, α, A, hr, hα, hα1, hA, ?_⟩
  intro x hx y hy
  have hx₀ := closedBall_subset_closedBall hrr hx
  have hy₀ := closedBall_subset_closedBall hrr hy
  have hholder := hgrad x hx₀ y hy₀
  have hdist : ‖y - x‖ ≤ 1 := by
    have hxn : ‖x - c‖ ≤ r := hx
    have hyn : ‖y - c‖ ≤ r := hy
    have htri := norm_sub_le_norm_sub_add_norm_sub y c x
    rw [norm_sub_rev c x] at htri
    linarith
  have hdα : ‖y - x‖ ≤ ‖y - x‖ ^ α :=
    Real.self_le_rpow_of_le_one (norm_nonneg _) hdist hα1
  have hux : |u y - u x| ≤ (L : ℝ) * ‖y - x‖ := by
    simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs] using hLip.dist_le_mul y x
  have hxG : gradient u x ∈ closedBall 0 (L : ℝ) := by
    simpa only [mem_closedBall, dist_zero_right] using norm_gradient_le_of_lipschitz hLip x
  have hyG : gradient u y ∈ closedBall 0 (L : ℝ) := by
    simpa only [mem_closedBall, dist_zero_right] using norm_gradient_le_of_lipschitz hLip y
  have hVdiff : |V (gradient u y) - V (gradient u x)| ≤
      (B : ℝ) * (H * ‖y - x‖ ^ α) := by
    have hh := hB.dist_le_mul (gradient u y) hyG (gradient u x) hxG
    simp only [dist_eq_norm, Real.norm_eq_abs] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hholder B.coe_nonneg)
  have hFdiff : |F y - F x| ≤ ((L : ℝ) + (B : ℝ) * H) * ‖y - x‖ ^ α := by
    calc
      _ = |-(u y - u x) + (V (gradient u y) - V (gradient u x))| := by
        congr 1
        dsimp [F]
        ring
      _ ≤ |u y - u x| + |V (gradient u y) - V (gradient u x)| := by
        simpa only [abs_neg] using abs_add_le (-(u y - u x)) (V (gradient u y) - V (gradient u x))
      _ ≤ (L : ℝ) * ‖y - x‖ + (B : ℝ) * (H * ‖y - x‖ ^ α) := add_le_add hux hVdiff
      _ ≤ ((L : ℝ) + (B : ℝ) * H) * ‖y - x‖ ^ α := by
        nlinarith [mul_le_mul_of_nonneg_left hdα L.coe_nonneg]
  have hexp : |Real.exp (F y) - Real.exp (F x)| ≤ (E : ℝ) * |F y - F x| := by
    simpa only [Real.dist_eq] using hE.dist_le_mul (F y) (mem_image_of_mem F hy) (F x) (mem_image_of_mem F hx)
  have hexp' := hexp.trans (mul_le_mul_of_nonneg_left hFdiff E.coe_nonneg)
  simp only [momentMongeAmpereDensity, ENNReal.toReal_ofReal (Real.exp_nonneg _)]
  change |Real.exp (F y) - Real.exp (F x)| ≤ A * ‖y - x‖ ^ α
  have hnonneg := Real.rpow_nonneg (norm_nonneg (y - x)) α
  dsimp [A]
  nlinarith

end KLS
end

#print axioms KLS.exists_local_momentMongeAmpereDensity_holder_bound

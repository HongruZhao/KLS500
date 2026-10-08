import KLS.WeakMomentSmoothAverageComparison
import KLS.MollifiedAverageMaximizers

open MeasureTheory Set Filter Matrix
open scoped Topology ContDiff NNReal
noncomputable section
namespace KLS
variable {n : ℕ}

/-- Genuine weak moment transport admits a penalized finite-difference maximum
at which the nonlinear log-density comparison holds. The comparison is derived
from actual smooth convolutions and their bounded maximizing subsequence. -/
theorem exists_weak_moment_maximum_with_target_comparison
    {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : Continuous V)
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    (h : Space n) {η : ℝ} (hη : 0 < η) :
    ∃ x : Space n,
      (∀ y, symmetricSecondDifference u h y - η * u y ≤
        symmetricSecondDifference u h x - η * u x) ∧
      symmetricSecondDifference (fun z => V (gradient u z)) h x ≤
        symmetricSecondDifference u h x + η * n := by
  let α := 1 + η/2
  have hα1 : 1 < α := by dsimp [α]; linarith
  have hα : 0 < α := zero_lt_one.trans hα1
  obtain ⟨x,s,x₀,hs,hlim,hmax,hmax₀⟩ :=
    exists_mollified_average_maximum_subsequence hLip hc h hα1
  let f := fun z => -u z + V (gradient u z)
  have hg := continuous_gradient_of_subsingleton_convexSubgradient hLip hc
    (moment_convexSubgradient_subsingleton_closedTarget hLip hc hV hK hKc hpush)
  have hf : Continuous f := hLip.continuous.neg.add (hV.comp hg)
  have hb (k : ℕ) : translatedAverage (mollify k f) h (x k) ≤
      f (x k) + n * Real.log α := by
    obtain ⟨hpos,hdet⟩ := weak_moment_mollified_average_det_lower hLip hc hV hK hKc hpush k h (x k)
    exact weak_moment_smooth_comparison_at_max hLip hc hV hK hKc hpush
      (translatedAverage_contDiff ((mollify_contDiff hLip.continuous.locallyIntegrable k).of_le (by simp)) h)
      hα (x k) (hmax k) hpos hdet
  have hb₀ : translatedAverage f h x₀ ≤ f x₀ + n * Real.log α :=
    le_of_tendsto_of_tendsto
      (translatedAverage_mollify_tendsto_at_moving_points hf h hlim hs.tendsto_atTop)
      (((hf.tendsto x₀).comp hlim).add_const (n * Real.log α))
      (Eventually.of_forall fun k => hb (s k))
  refine ⟨x₀,?_,?_⟩
  · intro y
    have hh := hmax₀ y
    dsimp [α,translatedAverage,symmetricSecondDifference] at *
    nlinarith
  · have hl := Real.log_le_sub_one_of_pos hα
    have hln := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    dsimp [f,α,translatedAverage,symmetricSecondDifference] at *
    nlinarith

end KLS
end

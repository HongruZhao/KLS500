import KLS.ConvexTraceDistribution

open MeasureTheory Set Filter Matrix
open scoped Topology ContDiff NNReal
noncomputable section
namespace KLS
variable {n : ℕ}

/-- The actual weak moment-map equation implies all linear trace inequalities
in distributions, with its genuine continuous log-density on the right side. -/
theorem weak_moment_distribution_trace_bound
    {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : Continuous V)
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    (J : Matrix (Fin n) (Fin n) ℝ) (hJ : J.PosDef)
    {χ : Space n → ℝ} (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ)
    (hχ0 : ∀ x, 0 ≤ χ x) :
    (∫ x, (-u x + V (gradient u x) + Real.log J.det + n) * χ x) ≤
      ∫ x, u x * (J * coordinateHessian χ x).trace := by
  have hg := continuous_gradient_of_subsingleton_convexSubgradient hLip hc
    (moment_convexSubgradient_subsingleton_closedTarget hLip hc hV hK hKc hpush)
  have hu := hLip.continuous
  have hf : Continuous (fun x => -u x + V (gradient u x) + Real.log J.det + n) := by
    fun_prop
  apply integral_trace_lower_of_convex_upper_tests hc hf hJ.posSemidef ?_ hχ hχc hχ0
  intro x ψ hψ hm
  let Ψ := fun y => ψ y + (u x - ψ x)
  have hΨ : ContDiffAt ℝ 2 Ψ x := ((hψ.add contDiff_const).of_le (by simp)).contDiffAt
  have hcontact : u x = Ψ x := by dsimp [Ψ]; ring
  have htouch : ∀ᶠ y in 𝓝 x, u y ≤ Ψ y := by
    filter_upwards [hm] with y hy
    change u y - ψ y ≤ u x - ψ x at hy
    dsimp [Ψ]
    linarith
  have hh := weak_moment_upper_test_trace_bound hLip hc hV hK hKc hpush hΨ hcontact htouch J hJ
  simpa only [Ψ,coordinateHessian_add_const] using hh

end KLS
end

import KLS.MomentPrimalC1

/-! The two actual gradients are continuous inverse maps between the full
source and the true finite-conjugate interior. -/

open MeasureTheory InnerProductSpace Set Filter Metric
open scoped Topology NNReal ENNReal

noncomputable section
namespace KLS

variable {n : ℕ}

theorem moment_gradient_mem_interior_domain
    {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : Continuous V)
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    (x : Space n) : gradient u x ∈ interior (momentLegendreDomain u) := by
  have hd := (moment_contDiff_one_closedTarget hLip hc hV hK hKc hpush).differentiable (by norm_num)
  exact moment_convexSubgradient_subset_interior_domain hLip hc hV hK.measurableSet hKc hpush x
    (gradient_mem_convexSubgradient hc (hd x))

theorem moment_gradient_finiteLegendrePotential_gradient
    {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : Continuous V)
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    (x : Space n) : gradient (finiteLegendrePotential u) (gradient u x) = x := by
  have hd := (moment_contDiff_one_closedTarget hLip hc hV hK hKc hpush).differentiable (by norm_num)
  exact gradient_finiteLegendrePotential_eq_of_mem_convexSubgradient hLip.continuous
    (moment_strictConvexOn hLip hc hV hK.measurableSet hKc hpush)
    (moment_gradient_mem_interior_domain hLip hc hV hK hKc hpush x)
    (gradient_mem_convexSubgradient hc (hd x))

theorem moment_gradient_gradient_finiteLegendrePotential
    {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : Continuous V)
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    {p : Space n} (hp : p ∈ interior (momentLegendreDomain u)) :
    gradient u (gradient (finiteLegendrePotential u) p) = p := by
  have hd := (moment_contDiff_one_closedTarget hLip hc hV hK hKc hpush).differentiable (by norm_num)
  exact (eq_gradient_of_mem_convexSubgradient (hd _)
    (mem_convexSubgradient_gradient_finiteLegendrePotential hLip.continuous
      (moment_strictConvexOn hLip hc hV hK.measurableSet hKc hpush) hp)).symm

def momentGradientHomeomorph
    {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : Continuous V)
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K) :
    Space n ≃ₜ interior (momentLegendreDomain u) where
  toFun x := ⟨gradient u x, moment_gradient_mem_interior_domain hLip hc hV hK hKc hpush x⟩
  invFun p := gradient (finiteLegendrePotential u) p
  left_inv := moment_gradient_finiteLegendrePotential_gradient hLip hc hV hK hKc hpush
  right_inv p := Subtype.ext (moment_gradient_gradient_finiteLegendrePotential hLip hc hV hK hKc hpush p.property)
  continuous_toFun := (continuous_gradient_of_subsingleton_convexSubgradient hLip hc
    (moment_convexSubgradient_subsingleton_closedTarget hLip hc hV hK hKc hpush)).subtype_mk _
  continuous_invFun := (continuousOn_gradient_finiteLegendrePotential_of_strictConvexOn hLip.continuous
    (moment_strictConvexOn hLip hc hV hK.measurableSet hKc hpush)).domRestrict

end KLS
end

#print axioms KLS.moment_gradient_mem_interior_domain
#print axioms KLS.moment_gradient_finiteLegendrePotential_gradient
#print axioms KLS.moment_gradient_gradient_finiteLegendrePotential
#print axioms KLS.momentGradientHomeomorph

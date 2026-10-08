import KLS.WeakMomentFiniteDifferenceBound
import KLS.FiniteDifferenceGradient

open MeasureTheory Set
open scoped ContDiff NNReal
noncomputable section
namespace KLS
variable {n : ℕ}

/-- The actual weak moment potential has globally Lipschitz gradient. Both C1
and the finite-difference bound are derived from weak transport; no Hessian is
assumed. The coefficient sixteen is conservative. -/
theorem weak_moment_gradient_lipschitz_of_uniformlyConvex_target
    {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : ContDiff ℝ 1 V) (hVc : ConvexOn ℝ univ V)
    {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun p => V p - (κ / 2) * ‖p‖ ^ 2))
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K) :
    LipschitzWith (⟨16/κ, by positivity⟩ : ℝ≥0) (gradient u) := by
  let C : ℝ≥0 := ⟨4/κ, by positivity⟩
  have hd := (moment_contDiff_one_closedTarget hLip hc hV.continuous hK hKc hpush).differentiable
    (by norm_num)
  have hb (h x : Space n) : symmetricSecondDifference u h x ≤ (C : ℝ) * ‖h‖ ^ 2 := by
    convert weak_moment_symmetricSecondDifference_le_of_uniformlyConvex_target
      hLip hc hV hVc hκ hstrong hK hKc hpush h x using 1
    change (4/κ) * ‖h‖ ^ 2 = 4 * ‖h‖ ^ 2 / κ
    ring
  have hh := lipschitzWith_gradient_of_secondDifference hc hd hb
  have he : 4 * C = (⟨16/κ, by positivity⟩ : ℝ≥0) := by
    apply NNReal.coe_injective
    change 4 * (4/κ) = 16/κ
    ring
  exact he ▸ hh

end KLS
end

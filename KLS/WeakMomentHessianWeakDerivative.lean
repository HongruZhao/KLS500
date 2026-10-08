import KLS.WeakMomentCutoffDifferenceEnergy
import KLS.FiniteDifferenceCutoff

open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped Topology ContDiff NNReal ENNReal Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- Every compact C1 cutoff of every actual weak-moment Hessian entry has
 an actual L2 weak derivative in every coordinate. Both the increment energy
 and the weak derivative are derived from literal weak transport. -/
theorem weak_moment_cutoff_hessian_hasWeakCoordinateDerivative
    {u V χ : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : ContDiff ℝ 1 V) (hVc : ConvexOn ℝ univ V)
    {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun p => V p - (κ / 2) * ‖p‖ ^ 2))
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ) (i j k : Fin n) :
    ∃ g : Lp ℝ 2 (volume : Measure (Space n)),
      HasWeakCoordinateDerivative (fun x => χ x*coordinateHessian u x i j) k g := by
  have hG := weak_moment_gradient_lipschitz_of_uniformlyConvex_target
    hLip hc hV hVc hκ hstrong hK hKc hpush
  have hm : Measurable (fun x => coordinateHessian u x i j) :=
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp (measurable_coordinateHessian u))
  obtain ⟨M,_,hM⟩ := weak_moment_cutoff_hessian_increment_bound
    hLip hc hV hVc hκ hstrong hK hKc hpush hχ.continuous hχc
  apply exists_cutoff_weak_coordinateDerivative_of_difference_energy hm.aestronglyMeasurable
    (show (0 : ℝ) ≤ 16/κ by positivity)
    (Eventually.of_forall (fun x => coordinateHessian_entry_bound_of_gradient_lipschitz hG x i j)) hχ hχc k (M := M)
  intro m
  have hb := (hM (cutoffScale m • EuclideanSpace.single k 1) i j).2
  have hn : ‖cutoffScale m • (EuclideanSpace.single k 1 : Space n)‖^2 = cutoffScale m^2 := by
    rw [norm_smul,PiLp.norm_single]
    simp only [Real.norm_eq_abs,abs_one,mul_one,sq_abs]
  simpa only [hn] using hb

end KLS
end

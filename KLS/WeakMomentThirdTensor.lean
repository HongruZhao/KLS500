import KLS.WeakMomentLocalHessianWeakDerivative
import KLS.LocalWeakDerivativeGluing

open MeasureTheory Set Filter
open scoped ContDiff Topology ENNReal NNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- The actual weak-moment Hessian has coherent locally L2 weak derivatives
 on the whole space, obtained by uniqueness and gluing of actual cutoffs. -/
theorem weak_moment_exists_local_hessian_weakDerivative
    {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : ContDiff ℝ 1 V) (hVc : ConvexOn ℝ univ V)
    {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun p => V p - (κ / 2) * ‖p‖ ^ 2))
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    (i j k : Fin n) :
    ∃ g : Space n → ℝ,
      (∀ S : Set (Space n), IsCompact S → MemLp g 2 (volume.restrict S)) ∧
      HasLocalWeakCoordinateDerivative (fun x => coordinateHessian u x i j) g k := by
  apply exists_local_weakCoordinateDerivative_of_cutoffs k
  intro m
  exact weak_moment_cutoff_hessian_hasWeakCoordinateDerivative
    hLip hc hV hVc hκ hstrong hK hKc hpush
    ((smoothCutoff_contDiff m).of_le (by simp)) (smoothCutoff_hasCompactSupport m) i j k

/-- All entries of a single raw third tensor are genuine weak derivatives
 of the actual Hessian. The index order is derivative, row, column.
 No classical third derivatives or tensor symmetry are asserted here. -/
theorem weak_moment_exists_third_tensor
    {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : ContDiff ℝ 1 V) (hVc : ConvexOn ℝ univ V)
    {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun p => V p - (κ / 2) * ‖p‖ ^ 2))
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K) :
    ∃ T : Space n → Fin n → Fin n → Fin n → ℝ,
      (∀ k i j S, IsCompact S →
        MemLp (fun x => T x k i j) 2 (volume.restrict S)) ∧
      ∀ k i j, HasLocalWeakCoordinateDerivative
        (fun x => coordinateHessian u x i j) (fun x => T x k i j) k := by
  have hex (k i j : Fin n) := weak_moment_exists_local_hessian_weakDerivative
    hLip hc hV hVc hκ hstrong hK hKc hpush i j k
  choose T hT hTw using hex
  exact ⟨fun x k i j => T k i j x, hT, hTw⟩

end KLS
end

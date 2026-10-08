import KLS.WeakMomentHessianWeakDerivative

open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped Topology ContDiff NNReal ENNReal Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
open EllipticPdes.Regularity
variable {n : ℕ}

/-- On every compact set, each actual Hessian entry has an L2 representative
 of its weak coordinate derivative against all compact C1 tests supported
 there. This is local Sobolev regularity, with no classical third derivative
 or coherence between different compact sets asserted. -/
theorem weak_moment_local_hessian_weak_coordinateDerivative
    {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : ContDiff ℝ 1 V) (hVc : ConvexOn ℝ univ V)
    {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun p => V p - (κ / 2) * ‖p‖ ^ 2))
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    {S : Set (Space n)} (hS : IsCompact S) (i j k : Fin n) :
    ∃ g : Lp ℝ 2 (volume : Measure (Space n)),
      ∀ ψ : Space n → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ → tsupport ψ ⊆ S →
        (∫ x, coordinateHessian u x i j*coordinateDerivative ψ k x) = -(∫ x, g x*ψ x) := by
  obtain ⟨χ,hχ,hχ1,_⟩ := exists_isTestFn_one_nhdsSet_of_isCompact hS isOpen_univ (subset_univ S)
  obtain ⟨g,hg⟩ := weak_moment_cutoff_hessian_hasWeakCoordinateDerivative
    hLip hc hV hVc hκ hstrong hK hKc hpush (hχ.1.of_le (by simp)) hχ.2.1 i j k
  refine ⟨g,?_⟩
  intro ψ hψ hψc hψS
  rw [← hg ψ hψ hψc]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    change coordinateHessian u x i j * coordinateDerivative ψ k x =
      (χ x * coordinateHessian u x i j) * coordinateDerivative ψ k x
    by_cases hx : x ∈ tsupport (coordinateDerivative ψ k)
    · have hχx : χ x = 1 := hχ1.self_of_nhdsSet x (hψS (tsupport_coordinateDerivative_subset ψ k hx))
      rw [hχx,one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hx,mul_zero,mul_zero]

end KLS
end

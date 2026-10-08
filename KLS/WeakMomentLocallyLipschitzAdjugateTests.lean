import KLS.LocallyLipschitzDivergenceTests

open MeasureTheory Set Filter Matrix
open scoped Topology ContDiff NNReal ENNReal Matrix.Norms.Elementwise
noncomputable section
namespace KLS
variable {n : ℕ}

/-- Adjugate columns of the actual C1,1 Hessian are locally L2, with the bound
 obtained from the genuine gradient Lipschitz constant. -/
theorem memLp_adjugateHessian_on_compact_of_gradient_lipschitz
    {u : Space n → ℝ} {L G : ℝ≥0} (hLip : LipschitzWith L u)
    (hG : LipschitzWith G (gradient u)) {S : Set (Space n)} (hS : IsCompact S) (i j : Fin n) :
    MemLp (fun x => (coordinateHessian u x).adjugate i j) 2 (volume.restrict S) := by
  obtain ⟨C,hC,hbound,_⟩ := exists_uniform_adjugate_bound_of_gradient_lipschitz hLip hG
  have : IsFiniteMeasure (volume.restrict S) := ⟨by simpa using hS.measure_lt_top⟩
  have hmat : Measurable (fun x : Space n => (coordinateHessian u x).adjugate) :=
    (show Continuous (fun A : Matrix (Fin n) (Fin n) ℝ => A.adjugate) from
      MatrixCalculus.contDiff_adjugate.continuous).measurable.comp (measurable_coordinateHessian u)
  have hm := (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hmat)
  apply (memLp_const C).mono' hm.aestronglyMeasurable
  exact Eventually.of_forall fun x => by
    change ‖(coordinateHessian u x).adjugate i j‖ ≤ C
    exact (Matrix.norm_le_iff hC).mp (hbound x) i j

/-- The actual weak moment adjugate divergence identity holds for all compact
 locally Lipschitz tests, with their actual coordinate derivatives. -/
theorem weak_moment_adjugateHessian_integral_column_locallyLipschitz
    {u V ψ : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : ContDiff ℝ 1 V) (hVc : ConvexOn ℝ univ V)
    {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun p => V p - (κ / 2) * ‖p‖ ^ 2))
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    (hψ : LocallyLipschitz ψ) (hψc : HasCompactSupport ψ) (j : Fin n) :
    (∑ i, ∫ x, (coordinateHessian u x).adjugate i j * coordinateDerivative ψ i x) = 0 := by
  have hG := weak_moment_gradient_lipschitz_of_uniformlyConvex_target
    hLip hc hV hVc hκ hstrong hK hKc hpush
  exact integral_divergence_zero_of_locallyLipschitz_test
    (fun i S hS => memLp_adjugateHessian_on_compact_of_gradient_lipschitz hLip hG hS i j)
    (fun φ hφ hφc => weak_moment_adjugateHessian_integral_column
      hLip hc hV hVc hκ hstrong hK hKc hpush hφ hφc j) hψ hψc

end KLS
end

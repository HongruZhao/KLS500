import KLS.WeakMomentTraceSquareBound
import KLS.RawMomentMapCompactLimit
import KLS.SymmetricMatrixApproximation

open MeasureTheory ProbabilityTheory InnerProductSpace Matrix Set
open scoped ContDiff NNReal
noncomputable section
namespace KLS
variable {n : ℕ}

/-- The actual C1,1 Stein coupling and the raw trace bound give the
 certified quadratic coefficient eight for a literal weak moment map. -/
theorem quadraticVarianceEight_of_weak_uniform_momentMap
    {μ : Measure (Space n)} {u V : Space n → ℝ} {L : ℝ≥0}
    [IsProbabilityMeasure (potentialMeasure u)]
    (hμ : admissibleMeasure μ) (hcompact : IsCompact μ.support)
    (hLip : LipschitzWith L u) (hc : ConvexOn ℝ univ u)
    (hV : ContDiff ℝ 2 V) (hVc : ConvexOn ℝ univ V)
    {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun p => V p - (κ / 2) * ‖p‖ ^ 2))
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (htarget : μ = (potentialMeasure V).restrict K)
    (hpush : MomentMap.gradientPushforward u = μ) : QuadraticVarianceEight μ := by
  let : IsProbabilityMeasure μ := hμ.isProb
  have htransport := hpush.trans htarget
  have hu := moment_contDiff_one_closedTarget hLip hc hV.continuous hK hKc htransport
  have hG := weak_moment_gradient_lipschitz_of_uniformlyConvex_target
    hLip hc (hV.of_le (by norm_num)) hVc hκ hstrong hK hKc htransport
  have hiso : IsIsotropic (MomentMap.gradientPushforward u) := by
    simpa only [hpush] using hμ.isotropic
  apply hμ.logConcave.quadraticVarianceEight_of_invertible
  intro M hM hMdet
  obtain ⟨A, U, B, _, hU, hBsym, horth, hAA, hpull, hnorm⟩ :=
    exists_spectral_quadratic_transport M hM
  have hA : A.det ≠ 0 := by
    intro hz
    apply hMdet
    rw [← hpull, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hz]
    ring
  have hB : B.PosSemidef := by
    rw [← hAA]
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self A
  have htrace := (weak_moment_trace_square_le_twice_trace
    hLip hc hV hVc hκ hstrong hK hKc htransport hiso hB).2
  have hstein := quadratic_variance_le_raw_hessian_contraction_of_compact_target_C11
    hμ hcompact hu hpush hG M A U hA hU horth hpull
  simp only [hAA] at hstein
  change ProbabilityTheory.variance (matrixQuadratic M) μ ≤
    4 * (∫ x, rawHessianTraceSquare (coordinateHessian u x) B ∂potentialMeasure u) at hstein
  rw [← matrixFrobeniusSq_eq_trace_sq hBsym, hnorm] at htrace
  linarith

end KLS
end

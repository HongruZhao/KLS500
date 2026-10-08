import KLS.RawMomentMapGaussianStein
import KLS.RawMomentMapContraction
import KLS.GaussianMomentMapLimit

/-!
The actual Gaussian Stein coupling for a C1 source with globally Lipschitz gradient
passes to zero Gaussian noise and then through the spectral affine pullback.
The source potential is never upgraded to C2.
-/
open MeasureTheory ProbabilityTheory InnerProductSpace Matrix Set Filter
open scoped ContDiff Topology BigOperators RealInnerProductSpace NNReal
noncomputable section
namespace KLS

theorem quadratic_variance_le_raw_momentMap_energy_of_compact_C11 {n : ℕ}
    {φ : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 1 φ) (hiso : IsIsotropic (MomentMap.gradientPushforward φ))
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hLC : measureLogConcave (MomentMap.linearGradientPushforward φ A))
    (hAC : MomentMap.linearGradientPushforward φ A ≪ volume)
    (hc : IsCompact (MomentMap.linearGradientPushforward φ A).support)
    {G : ℝ≥0} (hG : LipschitzWith G (gradient φ))
    (U : Matrix (Fin n) (Fin n) ℝ) (hU : U.IsSymm) :
    ProbabilityTheory.variance (matrixQuadratic U) (MomentMap.linearGradientPushforward φ A) ≤
      4 * ∑ i : Fin n, ∫ x,
        ‖MomentMap.rawTransportedHessianDerivative φ A x (WithLp.toLp 2 (U i))‖ ^ 2
          ∂potentialMeasure φ := by
  let ν := MomentMap.linearGradientPushforward φ A
  let : IsProbabilityMeasure ν := by
    dsimp [ν, MomentMap.linearGradientPushforward, MomentMap.gradientPushforward]
    infer_instance
  have hv := hLC.tendsto_quadraticVariance_gaussianSmoothing hAC hc U
  have he : Tendsto (fun k => 4 * ∑ i : Fin n, ∫ x,
      ‖MomentMap.rawTransportedHessianDerivative φ A x (WithLp.toLp 2 (U i)) +
        cutoffScale k ^ 2 • WithLp.toLp 2 (U i)‖ ^ 2 ∂potentialMeasure φ)
      atTop (𝓝 (4 * ∑ i : Fin n, ∫ x,
        ‖MomentMap.rawTransportedHessianDerivative φ A x (WithLp.toLp 2 (U i))‖ ^ 2
          ∂potentialMeasure φ)) := by
    apply Tendsto.const_mul
    apply tendsto_finsetSum
    intro i _
    simpa only [Function.comp_def] using
      (tendsto_integral_norm_add_smul_sq
        (MomentMap.memLp_rawTransportedHessianDerivative
          (μ := potentialMeasure φ) hG A (WithLp.toLp 2 (U i)) 2)
        (WithLp.toLp 2 (U i))).comp cutoffScale_tendsto_zero
  apply le_of_tendsto_of_tendsto hv he
  apply Eventually.of_forall
  intro k
  have hr := (cutoffScale_pos k).ne'
  have hp := gaussianSmoothing_eq_potentialMeasure_of_absolutelyContinuous hAC hc hr
  let : IsProbabilityMeasure (potentialMeasure (gaussianSmoothedPotential ν (cutoffScale k))) := by
    rw [← hp]
    infer_instance
  have hq : MemLp (matrixQuadratic U) 2
      (potentialMeasure (gaussianSmoothedPotential ν (cutoffScale k))) := by
    rw [← hp]
    exact (hLC.gaussianSmoothing_of_absolutelyContinuous hAC hc hr).memLp_two_matrixQuadratic U
  have hb := quadratic_variance_le_smoothed_raw_momentMap_energy_C11 hφ hiso
    ((gaussianSmoothedPotential_contDiff hc hr).of_le (by simp))
    (hLC.gaussianSmoothedPotential_convex_of_absolutelyContinuous hAC hc hr)
    A (cutoffScale k) hp hG U hU hq
  rwa [← hp] at hb

/-- The actual spectral pullback now needs only a compact original target.
The source representation and bounded source Hessian remain explicit. -/
theorem quadratic_variance_le_raw_hessian_contraction_of_compact_target_C11 {n : ℕ}
    {μ : Measure (Space n)} {φ : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hμ : admissibleMeasure μ) (hc : IsCompact μ.support) (hφ : ContDiff ℝ 1 φ)
    (hpush : MomentMap.gradientPushforward φ = μ)
    {G : ℝ≥0} (hG : LipschitzWith G (gradient φ))
    (M A U : Matrix (Fin n) (Fin n) ℝ) (hA : A.det ≠ 0)
    (hU : U.IsSymm) (horth : U.transpose * U = 1)
    (hpull : A.transpose * U * A = M) :
    ProbabilityTheory.variance (matrixQuadratic M) μ ≤
      4 * ∫ x, (A.transpose * A * coordinateHessian φ x *
        (A.transpose * A) * coordinateHessian φ x).trace ∂potentialMeasure φ := by
  let : IsProbabilityMeasure μ := hμ.isProb
  have hiso : IsIsotropic (MomentMap.gradientPushforward φ) := by
    simpa only [hpush] using hμ.isotropic
  have hlaw : MomentMap.linearGradientPushforward φ A = μ.map (matrixAction A) := by
    rw [MomentMap.linearGradientPushforward, hpush]
  have hLC : measureLogConcave (MomentMap.linearGradientPushforward φ A) := by
    rw [hlaw]
    exact hμ.logConcave.map_continuousAffineMap (matrixAction A).toContinuousAffineMap
  have hAC : MomentMap.linearGradientPushforward φ A ≪ volume := by
    rw [hlaw]
    exact absolutelyContinuous_map_matrixAction hμ.absolutelyContinuousLebesgue A hA
  have hc' : IsCompact (MomentMap.linearGradientPushforward φ A).support := by
    rw [hlaw]
    exact isCompact_support_map_matrixAction hc A
  have hb := quadratic_variance_le_raw_momentMap_energy_of_compact_C11 hφ hiso A hLC hAC hc' hG U hU
  rw [MomentMap.sum_integral_rawTransportedHessianDerivative_sq_C11 hφ hG A U horth] at hb
  rwa [hlaw, variance_matrixQuadratic_map, hpull] at hb


end KLS
end

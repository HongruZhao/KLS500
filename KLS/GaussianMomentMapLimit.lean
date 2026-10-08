import KLS.GaussianMomentMapStein
import KLS.GaussianSmoothingGeneral
import KLS.MatrixActionMeasure
import KLS.QuadraticTransportMeasure

/-!
# Removing Gaussian noise in the compact-target Stein argument

The target quadratic variance and the actual coupling energy converge as
the Gaussian scale vanishes. This gives the transported moment-map bound
for compact target laws without requiring a global smooth target potential
or a diffusion-range assumption for the unsmoothed law.
-/

open MeasureTheory ProbabilityTheory InnerProductSpace Matrix Set Filter
open scoped ContDiff Topology BigOperators RealInnerProductSpace

noncomputable section
namespace KLS

lemma integral_norm_add_smul_sq {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → Space n}
    (hT : MemLp T 2 μ) (w : Space n) (r : ℝ) :
    (∫ x, ‖T x + r ^ 2 • w‖ ^ 2 ∂μ) =
      (∫ x, ‖T x‖ ^ 2 ∂μ) + (2 * r ^ 2) * (∫ x, inner ℝ (T x) w ∂μ) +
        r ^ 4 * ‖w‖ ^ 2 := by
  have hi := integrable_inner_of_memLp_two hT (memLp_const w)
  have he (x : Ω) : ‖T x + r ^ 2 • w‖ ^ 2 =
      ‖T x‖ ^ 2 + (2 * r ^ 2) * inner ℝ (T x) w + r ^ 4 * ‖w‖ ^ 2 := by
    rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg r)]
    ring
  simp_rw [he]
  have hs : Integrable (fun x => ‖T x‖ ^ 2 + (2 * r ^ 2) * inner ℝ (T x) w) μ :=
    hT.norm.integrable_sq.add (hi.const_mul (2 * r ^ 2))
  rw [integral_add hs (integrable_const (r ^ 4 * ‖w‖ ^ 2)),
    integral_add hT.norm.integrable_sq (hi.const_mul (2 * r ^ 2)), integral_const_mul]
  simp

theorem tendsto_integral_norm_add_smul_sq {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → Space n}
    (hT : MemLp T 2 μ) (w : Space n) :
    Tendsto (fun r : ℝ => ∫ x, ‖T x + r ^ 2 • w‖ ^ 2 ∂μ)
      (𝓝 0) (𝓝 (∫ x, ‖T x‖ ^ 2 ∂μ)) := by
  simp_rw [integral_norm_add_smul_sq hT w]
  have hh : Continuous (fun r : ℝ =>
      (∫ x, ‖T x‖ ^ 2 ∂μ) + (2 * r ^ 2) * (∫ x, inner ℝ (T x) w ∂μ) +
        r ^ 4 * ‖w‖ ^ 2) := by fun_prop
  simpa using hh.tendsto 0

theorem quadratic_variance_le_linear_momentMap_energy_of_compact {n : ℕ}
    {φ : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hiso : IsIsotropic (MomentMap.gradientPushforward φ))
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hLC : measureLogConcave (MomentMap.linearGradientPushforward φ A))
    (hAC : MomentMap.linearGradientPushforward φ A ≪ volume)
    (hc : IsCompact (MomentMap.linearGradientPushforward φ A).support)
    {L : ℝ} (hL : ∀ x, ‖fderiv ℝ (gradient φ) x‖ ≤ L)
    (U : Matrix (Fin n) (Fin n) ℝ) (hU : U.IsSymm) :
    ProbabilityTheory.variance (matrixQuadratic U) (MomentMap.linearGradientPushforward φ A) ≤
      4 * ∑ i : Fin n, ∫ x,
        ‖MomentMap.transportedGradientDerivative φ A x (WithLp.toLp 2 (U i))‖ ^ 2
          ∂potentialMeasure φ := by
  let ν := MomentMap.linearGradientPushforward φ A
  let : IsProbabilityMeasure ν := by
    dsimp [ν, MomentMap.linearGradientPushforward, MomentMap.gradientPushforward]
    infer_instance
  have hv := hLC.tendsto_quadraticVariance_gaussianSmoothing hAC hc U
  have he : Tendsto (fun k => 4 * ∑ i : Fin n, ∫ x,
      ‖MomentMap.transportedGradientDerivative φ A x (WithLp.toLp 2 (U i)) +
        cutoffScale k ^ 2 • WithLp.toLp 2 (U i)‖ ^ 2 ∂potentialMeasure φ)
      atTop (𝓝 (4 * ∑ i : Fin n, ∫ x,
        ‖MomentMap.transportedGradientDerivative φ A x (WithLp.toLp 2 (U i))‖ ^ 2
          ∂potentialMeasure φ)) := by
    apply Tendsto.const_mul
    apply tendsto_finsetSum
    intro i _
    simpa only [Function.comp_def] using
      (tendsto_integral_norm_add_smul_sq
        (MomentMap.memLp_transportedGradientDerivative
          (MomentMap.contDiff_gradient_of_contDiff_two hφ) hL A (WithLp.toLp 2 (U i)))
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
  have hb := quadratic_variance_le_smoothed_linear_momentMap_energy hφ hiso
    ((gaussianSmoothedPotential_contDiff hc hr).of_le (by simp))
    (hLC.gaussianSmoothedPotential_convex_of_absolutelyContinuous hAC hc hr)
    A (cutoffScale k) hp hL U hU hq
  rwa [← hp] at hb

/-- The actual spectral pullback now needs only a compact original target.
The source representation and bounded source Hessian remain explicit. -/
theorem quadratic_variance_le_hessian_contraction_of_compact_target {n : ℕ}
    {μ : Measure (Space n)} {φ : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hμ : admissibleMeasure μ) (hc : IsCompact μ.support) (hφ : ContDiff ℝ 2 φ)
    (hpush : MomentMap.gradientPushforward φ = μ)
    {L : ℝ} (hL : ∀ x, ‖fderiv ℝ (gradient φ) x‖ ≤ L)
    (M A U : Matrix (Fin n) (Fin n) ℝ) (hA : A.det ≠ 0)
    (hU : U.IsSymm) (horth : U.transpose * U = 1)
    (hpull : A.transpose * U * A = M) :
    ProbabilityTheory.variance (matrixQuadratic M) μ ≤
      4 * ∫ x, (A.transpose * A * MomentMap.hessianMatrix φ x *
        (A.transpose * A) * MomentMap.hessianMatrix φ x).trace ∂potentialMeasure φ := by
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
  have hb := quadratic_variance_le_linear_momentMap_energy_of_compact hφ hiso A hLC hAC hc' hL U hU
  rw [MomentMap.sum_integral_transportedGradientDerivative_sq hφ hL A U horth] at hb
  rwa [hlaw, variance_matrixQuadratic_map, hpull] at hb

end KLS
end

#print axioms KLS.tendsto_integral_norm_add_smul_sq
#print axioms KLS.quadratic_variance_le_linear_momentMap_energy_of_compact
#print axioms KLS.quadratic_variance_le_hessian_contraction_of_compact_target

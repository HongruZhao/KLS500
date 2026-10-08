import OptCombinedSuspensionDirection

/-! The derivative in the pure-copy subspace is computed from the actual
suspension log-Laplace factorization, including every independent copy. -/
open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology BigOperators
noncomputable section
namespace KLS
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

lemma suspension_logLaplace_pureProjection {n N : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : NormExponentialDomain μ (fun _ => 1))
    {f : Space n → ℝ} (hf : Measurable f) {A B : ℝ}
    (hbound : ∀ x, |f x| ≤ A + B * ‖x‖) {β : ℝ} (hβ : 0 < β)
    (σ c : ℝ) (q : Space (suspensionDimension n N)) :
    tiltLogLaplace (euclideanSuspensionLaw (N := N) μ f β σ c)
      (suspensionPureProjection n N q) =
        ∑ i, tiltLogLaplace μ (suspensionCopyProjection n N i q) := by
  have hq : |suspensionNoiseProjection n N (suspensionPureProjection n N q) / σ| < β := by
    simpa only [suspensionNoiseProjection_pureProjection, zero_div, abs_zero] using hβ
  rw [suspension_logLaplace_factorization hμ hf hbound hβ σ c _ hq]
  have he (i : Fin N) :
      suspensionCopyGraphParameter n N σ c i (suspensionPureProjection n N q) =
        suspensionGraphParameter n (0, suspensionCopyProjection n N i q) := by
    simp [suspensionCopyGraphParameter, suspensionNoiseProjection_pureProjection,
      suspensionCopyProjection_pureProjection]
  have hg (z : Space n) : tiltLogLaplace (μ.map (suspensionGraph f))
      (suspensionGraphParameter n (0,z)) = tiltLogLaplace μ z := by
    unfold tiltLogLaplace
    rw [graph_tiltPartition_at_zero_signal hf]
  simp_rw [he, hg]
  simp only [suspensionNoiseProjection_pureProjection, zero_div, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    sub_zero, div_self (pow_ne_zero 2 hβ.ne'), Real.log_one, add_zero]

lemma fderiv_suspension_logLaplace_pure {n N : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : NormExponentialDomain μ (fun _ => 1))
    {f : Space n → ℝ} (hf : Measurable f) {A B : ℝ}
    (hbound : ∀ x, |f x| ≤ A + B * ‖x‖) {β : ℝ} (hβ : 0 < β)
    (σ c : ℝ) (q v : Space (suspensionDimension n N))
    (hq : suspensionNoiseProjection n N q = 0) (hv : suspensionNoiseProjection n N v = 0) :
    fderiv ℝ (tiltLogLaplace (euclideanSuspensionLaw (N := N) μ f β σ c)) q v =
      ∑ i, fderiv ℝ (tiltLogLaplace μ) (suspensionCopyProjection n N i q)
        (suspensionCopyProjection n N i v) := by
  let G := tiltLogLaplace (euclideanSuspensionLaw (N := N) μ f β σ c)
  let Q := suspensionPureProjection n N
  have hQq : Q q = q := suspensionPureProjection_eq_self q hq
  have hQv : Q v = v := suspensionPureProjection_eq_self v hv
  have hG : DifferentiableAt ℝ G q :=
    (contDiffAt_suspension_logLaplace hμ hf hbound hβ σ c q hq).differentiableAt (by simp)
  have hbase : Differentiable ℝ (tiltLogLaplace μ) :=
    (contDiff_tiltLogLaplace_of_normExponentialDomain hμ).differentiable (by simp)
  have hsum : HasFDerivAt (fun z => ∑ i, tiltLogLaplace μ (suspensionCopyProjection n N i z))
      (∑ i, (fderiv ℝ (tiltLogLaplace μ) (suspensionCopyProjection n N i q)).comp
        (suspensionCopyProjection n N i)) q :=
    HasFDerivAt.fun_sum (fun i _ => (hbase _).hasFDerivAt.comp q (suspensionCopyProjection n N i).hasFDerivAt)
  have hG' : DifferentiableAt ℝ G (Q q) := by rwa [hQq]
  have hGQ := hG'.hasFDerivAt.comp q Q.hasFDerivAt
  rw [hQq] at hGQ
  simp only [Function.comp_def] at hGQ
  have heq : (fun z => G (Q z)) =
      (fun z => ∑ i, tiltLogLaplace μ (suspensionCopyProjection n N i z)) := by
    funext z
    exact suspension_logLaplace_pureProjection hμ hf hbound hβ σ c z
  rw [heq] at hGQ
  have he := congrArg (fun L : Space (suspensionDimension n N) →L[ℝ] ℝ => L v) (hGQ.unique hsum)
  simpa only [ContinuousLinearMap.comp_apply, _root_.sum_apply, hQv] using he

lemma suspension_pure_derivative_on_block {n N : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : NormExponentialDomain μ (fun _ => 1)) (hiso : IsIsotropic μ)
    {f : Space n → ℝ} (hf : Measurable f) {A B : ℝ}
    (hbound : ∀ x, |f x| ≤ A + B * ‖x‖) {β : ℝ} (hβ : 0 < β)
    (σ c : ℝ) (i : Fin N) (z u : Space n) :
    fderiv ℝ (tiltLogLaplace (euclideanSuspensionLaw (N := N) μ f β σ c))
      (suspensionBlockEmbedding n N i z) (suspensionCombinedDirection n N 0 u) =
        (Real.sqrt N)⁻¹ * ∫ x, inner ℝ x u ∂exponentialTilt μ z := by
  rw [fderiv_suspension_logLaplace_pure hμ hf hbound hβ σ c _ _
    (suspensionNoiseProjection_blockEmbedding n N i z)
    (suspensionNoiseProjection_combinedDirection n N 0 u)]
  simp_rw [suspensionCopyProjection_combinedDirection, map_smul, smul_eq_mul]
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_eq_single i]
  · rw [suspensionCopyProjection_blockEmbedding, ite_eq_left rfl,
      fderiv_tiltLogLaplace_direction_of_normExponentialDomain hμ]
  · intro j _ hji
    rw [suspensionCopyProjection_blockEmbedding, ite_eq_right hji,
      fderiv_tiltLogLaplace_direction_of_normExponentialDomain hμ, exponentialTilt_zero]
    exact hiso.integral_inner u
  · simp

end KLS
end

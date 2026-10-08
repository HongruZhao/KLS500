import KLS.SuspensionLaplaceFactorization

/-! The actual derivative of the suspension log-Laplace transform along its
extra coordinate, throughout the zero-extra-parameter subspace. -/

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology BigOperators
noncomputable section
namespace KLS

def suspensionNoiseDirection (n N : ℕ) : Space (suspensionDimension n N) :=
  EuclideanSpace.basisFun (Fin (suspensionDimension n N)) ℝ
    (Fintype.equivFin (SuspensionIndex n N) none)

lemma suspensionNoiseProjection_noiseDirection (n N : ℕ) :
    suspensionNoiseProjection n N (suspensionNoiseDirection n N) = 1 := by
  simp [suspensionNoiseProjection, suspensionNoiseDirection]

lemma suspensionCopyProjection_noiseDirection (n N : ℕ) (i : Fin N) :
    suspensionCopyProjection n N i (suspensionNoiseDirection n N) = 0 := by
  ext j
  simp [suspensionCopyProjection, suspensionNoiseDirection]

lemma suspensionGraphParameter_one_zero (n : ℕ) :
    suspensionGraphParameter n (1, 0) = EuclideanSpace.basisFun (Fin (n + 1)) ℝ 0 := by
  ext j
  refine Fin.cases ?_ (fun k => ?_) j <;>
    simp [suspensionGraphParameter]

lemma suspensionCopyGraphParameter_noiseDirection (n N : ℕ) (σ c : ℝ) (i : Fin N) :
    suspensionCopyGraphParameter n N σ c i (suspensionNoiseDirection n N) =
      (c / σ) • EuclideanSpace.basisFun (Fin (n + 1)) ℝ 0 := by
  simp only [suspensionCopyGraphParameter, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, _root_.smul_apply, smul_eq_mul,
    suspensionNoiseProjection_noiseDirection, suspensionCopyProjection_noiseDirection, mul_one]
  rw [← suspensionGraphParameter_one_zero]
  have he : (c / σ, (0 : Space n)) = (c / σ) • ((1 : ℝ), (0 : Space n)) := by simp
  rw [he, map_smul]

lemma hasDerivAt_laplaceNoise_log_formula_zero {β : ℝ} (hβ : 0 < β) :
    HasDerivAt (fun t : ℝ => Real.log (β ^ 2 / (β ^ 2 - t ^ 2))) 0 0 := by
  have hden : β ^ 2 - (0 : ℝ) ^ 2 ≠ 0 := by simpa using pow_ne_zero 2 hβ.ne'
  have hd := ((hasDerivAt_const (0 : ℝ) (β ^ 2)).div
    ((hasDerivAt_const (0 : ℝ) (β ^ 2)).sub ((hasDerivAt_id (0 : ℝ)).pow 2)) hden).log
      (by simpa using div_ne_zero (pow_ne_zero 2 hβ.ne') hden)
  simpa using hd

lemma suspension_logLaplace_eventuallyEq {n N : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : NormExponentialDomain μ (fun _ => 1))
    {f : Space n → ℝ} (hf : Measurable f) {A B : ℝ}
    (hbound : ∀ x, |f x| ≤ A + B * ‖x‖) {β : ℝ} (hβ : 0 < β)
    (σ c : ℝ) (q : Space (suspensionDimension n N))
    (hq : suspensionNoiseProjection n N q = 0) :
    tiltLogLaplace (euclideanSuspensionLaw (N := N) μ f β σ c) =ᶠ[𝓝 q]
      (fun z => (∑ i, tiltLogLaplace (μ.map (suspensionGraph f))
        (suspensionCopyGraphParameter n N σ c i z)) +
        Real.log (β ^ 2 / (β ^ 2 - (suspensionNoiseProjection n N z / σ) ^ 2))) := by
  have hs : IsOpen {z : Space (suspensionDimension n N) |
      |suspensionNoiseProjection n N z / σ| < β} :=
    isOpen_lt (by fun_prop) continuous_const
  have hm : q ∈ {z : Space (suspensionDimension n N) |
      |suspensionNoiseProjection n N z / σ| < β} := by simpa [hq] using hβ
  filter_upwards [hs.mem_nhds hm] with z hz
  exact suspension_logLaplace_factorization hμ hf hbound hβ σ c z hz

lemma contDiffAt_suspension_logLaplace {n N : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : NormExponentialDomain μ (fun _ => 1))
    {f : Space n → ℝ} (hf : Measurable f) {A B : ℝ}
    (hbound : ∀ x, |f x| ≤ A + B * ‖x‖) {β : ℝ} (hβ : 0 < β)
    (σ c : ℝ) (q : Space (suspensionDimension n N))
    (hq : suspensionNoiseProjection n N q = 0) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (tiltLogLaplace (euclideanSuspensionLaw (N := N) μ f β σ c)) q := by
  have hg := contDiff_graphLogLaplace_of_linear_growth hμ hf hbound
  have hden : β ^ 2 - (suspensionNoiseProjection n N q / σ) ^ 2 ≠ 0 := by
    simpa [hq] using pow_ne_zero 2 hβ.ne'
  have hrat : ContDiffAt ℝ (⊤ : ℕ∞) (fun z : Space (suspensionDimension n N) =>
      β ^ 2 / (β ^ 2 - (suspensionNoiseProjection n N z / σ) ^ 2)) q :=
    contDiffAt_const.div (contDiffAt_const.sub (by fun_prop)) hden
  have hs : ContDiffAt ℝ (⊤ : ℕ∞) (fun z =>
      (∑ i, tiltLogLaplace (μ.map (suspensionGraph f))
        (suspensionCopyGraphParameter n N σ c i z)) +
        Real.log (β ^ 2 / (β ^ 2 - (suspensionNoiseProjection n N z / σ) ^ 2))) q :=
    (ContDiffAt.sum (fun i _ => hg.contDiffAt.comp q
      (suspensionCopyGraphParameter n N σ c i).contDiff.contDiffAt)).add
      (hrat.log (div_ne_zero (pow_ne_zero 2 hβ.ne') hden))
  exact hs.congr_of_eventuallyEq (suspension_logLaplace_eventuallyEq hμ hf hbound hβ σ c q hq)

lemma fderiv_suspension_logLaplace_noise {n N : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : NormExponentialDomain μ (fun _ => 1))
    {f : Space n → ℝ} (hf : Measurable f) {A B : ℝ}
    (hbound : ∀ x, |f x| ≤ A + B * ‖x‖) {β : ℝ} (hβ : 0 < β)
    (σ c : ℝ) (q : Space (suspensionDimension n N))
    (hq : suspensionNoiseProjection n N q = 0) :
    fderiv ℝ (tiltLogLaplace (euclideanSuspensionLaw (N := N) μ f β σ c)) q
      (suspensionNoiseDirection n N) =
        (c / σ) * ∑ i, ∫ x, f x ∂exponentialTilt μ (suspensionCopyProjection n N i q) := by
  let G := tiltLogLaplace (μ.map (suspensionGraph f))
  let P := suspensionCopyGraphParameter n N σ c
  have hG : Differentiable ℝ G :=
    (contDiff_graphLogLaplace_of_linear_growth hμ hf hbound).differentiable (by simp)
  have hsum : HasFDerivAt (fun z => ∑ i, G (P i z))
      (∑ i, (fderiv ℝ G (P i q)).comp (P i)) q :=
    HasFDerivAt.fun_sum (fun i _ => (hG (P i q)).hasFDerivAt.comp q (P i).hasFDerivAt)
  have hlin : HasFDerivAt (fun z => suspensionNoiseProjection n N z / σ)
      (σ⁻¹ • suspensionNoiseProjection n N) q := by
    convert (σ⁻¹ • suspensionNoiseProjection n N).hasFDerivAt (x := q) using 1
    ext z
    simp [div_eq_mul_inv, mul_comm]
  have hn : HasFDerivAt (𝕜 := ℝ) (fun z => Real.log
      (β ^ 2 / (β ^ 2 - (suspensionNoiseProjection n N z / σ) ^ 2))) 0 q := by
    have hd := (hasDerivAt_laplaceNoise_log_formula_zero hβ).comp_hasFDerivAt_of_eq q hlin
      (by simp [hq])
    simpa only [zero_smul, Function.comp_def] using hd
  have hd := (hsum.add hn).congr_of_eventuallyEq
    (suspension_logLaplace_eventuallyEq hμ hf hbound hβ σ c q hq)
  rw [hd.fderiv]
  simp only [add_zero, _root_.sum_apply, ContinuousLinearMap.comp_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change fderiv ℝ G (P i q) (suspensionCopyGraphParameter n N σ c i
    (suspensionNoiseDirection n N)) = _
  rw [suspensionCopyGraphParameter_noiseDirection, map_smul, smul_eq_mul]
  congr 1
  have he : P i q = suspensionGraphParameter n (0, suspensionCopyProjection n N i q) := by
    simp [P, suspensionCopyGraphParameter, hq]
  rw [he]
  exact fderiv_graphLogLaplace_first_at_zero_signal hμ hf hbound _

end KLS
end
#print axioms KLS.contDiffAt_suspension_logLaplace
#print axioms KLS.fderiv_suspension_logLaplace_noise

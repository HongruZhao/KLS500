import KLS.SuspensionGraphLogLaplace
import KLS.SuspensionIsotropy
import KLS.LaplaceNoiseLaplaceTransform

/-! Exact factorization of the log-Laplace transform of the literal suspension.
The finite-copy factors are graph transforms of the original noncompact law. -/

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology BigOperators
noncomputable section
namespace KLS

def suspensionNoiseProjection (n N : ℕ) : Space (suspensionDimension n N) →L[ℝ] ℝ :=
  EuclideanSpace.proj (Fintype.equivFin (SuspensionIndex n N) none)

def suspensionCopyProjection (n N : ℕ) (i : Fin N) :
    Space (suspensionDimension n N) →L[ℝ] Space n where
  toFun z := WithLp.toLp 2 (fun j => z (Fintype.equivFin _ (some (i, j))))
  map_add' _ _ := by ext j; rfl
  map_smul' _ _ := by ext j; rfl
  cont := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).comp
    exact continuous_pi (fun j => by fun_prop)

def suspensionCopyGraphParameter (n N : ℕ) (σ c : ℝ) (i : Fin N) :
    Space (suspensionDimension n N) →L[ℝ] Space (n + 1) :=
  (suspensionGraphParameter n).comp
    (((c / σ) • suspensionNoiseProjection n N).prod (suspensionCopyProjection n N i))

lemma inner_suspensionCoordinates {n N : ℕ} (q : Space (suspensionDimension n N))
    (p : (Fin N → Space n) × ℝ) :
    inner ℝ q (suspensionCoordinates n N p) =
      suspensionNoiseProjection n N q * p.2 +
        ∑ i, inner ℝ (suspensionCopyProjection n N i q) (p.1 i) := by
  rw [inner_eq_coordinate_sum, ← (Fintype.equivFin (SuspensionIndex n N)).sum_comp]
  simp_rw [suspensionCoordinates_apply]
  rw [Fintype.sum_option, Fintype.sum_prod_type]
  simp_rw [inner_eq_coordinate_sum]
  change p.2 * q (Fintype.equivFin _ none) + _ =
    q (Fintype.equivFin _ none) * p.2 + _
  rw [mul_comm p.2]
  rfl

lemma exp_inner_suspension_product {n N : ℕ} (f : Space n → ℝ) (σ c : ℝ)
    (q : Space (suspensionDimension n N)) (p : (Fin N → Space n) × ℝ) :
    Real.exp (inner ℝ q (suspensionCoordinates n N
      (p.1, suspensionExtra (fun x => c * ∑ i, f (x i)) σ p))) =
    (∏ i, Real.exp (inner ℝ (suspensionCopyGraphParameter n N σ c i q)
      (suspensionGraph f (p.1 i)))) *
      Real.exp ((suspensionNoiseProjection n N q / σ) * p.2) := by
  rw [inner_suspensionCoordinates, ← Real.exp_sum, ← Real.exp_add]
  congr 1
  simp only [suspensionCopyGraphParameter, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, _root_.smul_apply, smul_eq_mul,
    inner_suspensionGraphParameter, Finset.sum_add_distrib,
    ← Finset.mul_sum, suspensionExtra]
  ring

lemma suspension_tiltPartition_factorization {n N : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] {f : Space n → ℝ} (hf : Measurable f)
    {β : ℝ} (hβ : 0 < β) (σ c : ℝ) (q : Space (suspensionDimension n N)) :
    tiltPartition (euclideanSuspensionLaw (N := N) μ f β σ c) (fun x => inner ℝ q x) =
      (∏ i, tiltPartition (μ.map (suspensionGraph f))
        (fun y => inner ℝ (suspensionCopyGraphParameter n N σ c i q) y)) *
      (∫ s, Real.exp ((suspensionNoiseProjection n N q / σ) * s) ∂laplaceNoiseLaw β) := by
  have : IsProbabilityMeasure (laplaceNoiseLaw β) := isProbabilityMeasure_laplaceNoiseLaw hβ
  have hT : Measurable (fun p : (Fin N → Space n) × ℝ => suspensionCoordinates n N
      (p.1, suspensionExtra (fun x => c * ∑ i, f (x i)) σ p)) :=
    (suspensionCoordinates n N).measurable.comp (by unfold suspensionExtra; fun_prop)
  rw [euclideanSuspensionLaw_eq_product_map μ f hf, tiltPartition,
    integral_map hT.aemeasurable (by fun_prop)]
  simp_rw [exp_inner_suspension_product]
  rw [integral_prod_mul
    (fun x : Fin N → Space n => ∏ i, Real.exp
      (inner ℝ (suspensionCopyGraphParameter n N σ c i q) (suspensionGraph f (x i))))
    (fun s : ℝ => Real.exp ((suspensionNoiseProjection n N q / σ) * s)),
    integral_fintype_prod_eq_prod (fun i (x : Space n) => Real.exp
      (inner ℝ (suspensionCopyGraphParameter n N σ c i q) (suspensionGraph f x)))]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [tiltPartition, integral_map (measurable_suspensionGraph hf).aemeasurable (by fun_prop)]

lemma suspension_logLaplace_factorization {n N : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : NormExponentialDomain μ (fun _ => 1))
    {f : Space n → ℝ} (hf : Measurable f) {A B : ℝ}
    (hbound : ∀ x, |f x| ≤ A + B * ‖x‖) {β : ℝ} (hβ : 0 < β)
    (σ c : ℝ) (q : Space (suspensionDimension n N))
    (hq : |suspensionNoiseProjection n N q / σ| < β) :
    tiltLogLaplace (euclideanSuspensionLaw (N := N) μ f β σ c) q =
      (∑ i, tiltLogLaplace (μ.map (suspensionGraph f))
        (suspensionCopyGraphParameter n N σ c i q)) +
      Real.log (β ^ 2 / (β ^ 2 - (suspensionNoiseProjection n N q / σ) ^ 2)) := by
  have hg := normExponentialDomain_suspensionGraph hμ hf hbound
  have : IsProbabilityMeasure (μ.map (suspensionGraph f)) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_suspensionGraph hf).aemeasurable).2
      inferInstance
  have hp (i : Fin N) : 0 < tiltPartition (μ.map (suspensionGraph f))
      (fun y => inner ℝ (suspensionCopyGraphParameter n N σ c i q) y) :=
    integral_exp_pos (integrable_exp_inner_of_normExponentialDomain_one hg _)
  have hn : 0 < β ^ 2 / (β ^ 2 - (suspensionNoiseProjection n N q / σ) ^ 2) := by
    have hh := abs_lt.mp hq
    apply div_pos (sq_pos_of_pos hβ)
    nlinarith [sq_nonneg (β - |suspensionNoiseProjection n N q / σ|),
      sq_abs (suspensionNoiseProjection n N q / σ)]
  rw [tiltLogLaplace, suspension_tiltPartition_factorization hf hβ,
    integral_exp_mul_laplaceNoiseLaw hβ hq,
    Real.log_mul (Finset.prod_ne_zero_iff.mpr (fun i _ => (hp i).ne')) hn.ne',
    Real.log_prod (fun i _ => (hp i).ne')]
  rfl

end KLS
end
#print axioms KLS.suspension_logLaplace_factorization

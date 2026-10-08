import KLS.GaussianSmoothingMoments
import KLS.WeightedIntegrationByParts
import KLS.SmoothCutoffSequence

/-!
# Gaussian smoothing without isotropic normalization

The smooth positive density and convex potential require only an absolutely
continuous log-concave probability with compact support. Moment convergence
requires only a log-concave probability. This applies to invertible linear
images of an isotropic target without imposing isotropy again.
-/

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped ENNReal MeasureTheory ContDiff Topology BigOperators

noncomputable section
namespace KLS

theorem eq_withDensity_lowerBallDensity_of_absolutelyContinuous {n : ℕ}
    {μ : Measure (Space n)} [IsFiniteMeasure μ] (hμ : μ ≪ volume) :
    μ = volume.withDensity (lowerBallDensity μ) := by
  calc
    μ = volume.withDensity (μ.rnDeriv volume) :=
      (Measure.withDensity_rnDeriv_eq μ volume hμ).symm
    _ = volume.withDensity (lowerBallDensity μ) :=
      withDensity_congr_ae (lowerBallDensity_ae_eq_rnDeriv μ).symm

theorem ofReal_gaussianSmoothedDensity_of_absolutelyContinuous {n : ℕ}
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : μ ≪ volume)
    (hc : IsCompact μ.support) {r : ℝ} (hr : r ≠ 0) (x : Space n) :
    ENNReal.ofReal (gaussianSmoothedDensity μ r x) =
      (lowerBallDensity μ ⋆ₗ (fun z => ENNReal.ofReal (scaledGaussianKernel n r z))) x := by
  rw [gaussianSmoothedDensity,
    ofReal_integral_eq_lintegral_ofReal (integrable_scaledGaussianKernel_translate hc r x)
      (Eventually.of_forall fun y => (scaledGaussianKernel_pos hr (x - y)).le)]
  conv_lhs => rw [eq_withDensity_lowerBallDensity_of_absolutelyContinuous hμ]
  have hg : Measurable (fun y => ENNReal.ofReal (scaledGaussianKernel n r (x - y))) :=
    ((scaledGaussianKernel_contDiff n r).continuous.measurable.comp
      (measurable_const.sub measurable_id)).ennreal_ofReal
  rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_lowerBallDensity μ) hg]
  simp only [lconvolution, sub_eq_add_neg, add_comm, Pi.mul_apply]

theorem gaussianSmoothing_eq_withDensity_of_absolutelyContinuous {n : ℕ}
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : μ ≪ volume)
    (hc : IsCompact μ.support) {r : ℝ} (hr : r ≠ 0) : gaussianSmoothing μ r =
      (volume : Measure (Space n)).withDensity
        (fun x => ENNReal.ofReal (gaussianSmoothedDensity μ r x)) := by
  rw [gaussianSmoothing, scaledGaussianMeasure_eq_withDensity hr]
  conv_lhs => rw [eq_withDensity_lowerBallDensity_of_absolutelyContinuous hμ]
  rw [conv_withDensity_eq_lconvolution (measurable_lowerBallDensity μ)
    (scaledGaussianKernel_contDiff n r).continuous.measurable.ennreal_ofReal]
  congr 1
  funext x
  exact (ofReal_gaussianSmoothedDensity_of_absolutelyContinuous hμ hc hr x).symm

theorem measureLogConcave.gaussianSmoothedDensity_logConcave_of_absolutelyContinuous
    {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hμ : measureLogConcave μ) (hAC : μ ≪ volume) (hc : IsCompact μ.support)
    {r : ℝ} (hr : r ≠ 0) (x y : Space n) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ENNReal.ofReal (gaussianSmoothedDensity μ r x) ^ t *
      ENNReal.ofReal (gaussianSmoothedDensity μ r y) ^ (1 - t) ≤
        ENNReal.ofReal (gaussianSmoothedDensity μ r (t • x + (1 - t) • y)) := by
  simp_rw [ofReal_gaussianSmoothedDensity_of_absolutelyContinuous hAC hc hr]
  exact lconvolution_logConcave (measurable_lowerBallDensity μ)
    (scaledGaussianKernel_contDiff n r).continuous.measurable.ennreal_ofReal
    (fun x y _ ht0 ht1 => hμ.lowerBallDensity_logConcave x y ht0 ht1)
    (fun x y _ ht0 ht1 => scaledGaussianKernel_logConcave hr x y ht0 ht1) x y ht0 ht1

theorem measureLogConcave.gaussianSmoothedPotential_convex_of_absolutelyContinuous
    {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hμ : measureLogConcave μ) (hAC : μ ≪ volume) (hc : IsCompact μ.support)
    {r : ℝ} (hr : r ≠ 0) : ConvexOn ℝ univ (gaussianSmoothedPotential μ r) := by
  have hh := convexOn_realDensityPotential
    (d := fun x => ENNReal.ofReal (gaussianSmoothedDensity μ r x))
    (fun x => ENNReal.ofReal_lt_top)
    (fun x y _ ht0 ht1 => hμ.gaussianSmoothedDensity_logConcave_of_absolutelyContinuous
      hAC hc hr x y ht0 ht1)
  have hs : {x | 0 < ENNReal.ofReal (gaussianSmoothedDensity μ r x)} = univ := by
    ext x
    simp only [mem_ofPred_eq, mem_univ, iff_true, ENNReal.ofReal_pos]
    exact gaussianSmoothedDensity_pos hc hr x
  rw [hs] at hh
  convert hh using 1
  ext x
  simp only [realDensityPotential, ENNReal.toReal_ofReal
    (gaussianSmoothedDensity_pos hc hr x).le, gaussianSmoothedPotential]

theorem gaussianSmoothing_eq_potentialMeasure_of_absolutelyContinuous {n : ℕ}
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hAC : μ ≪ volume)
    (hc : IsCompact μ.support) {r : ℝ} (hr : r ≠ 0) :
    gaussianSmoothing μ r = potentialMeasure (gaussianSmoothedPotential μ r) := by
  rw [gaussianSmoothing_eq_withDensity_of_absolutelyContinuous hAC hc hr]
  congr 1
  funext x
  rw [gaussianSmoothedPotential, neg_neg, Real.exp_log (gaussianSmoothedDensity_pos hc hr x)]

theorem measureLogConcave.gaussianSmoothing_of_absolutelyContinuous {n : ℕ}
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hμ : measureLogConcave μ) (hAC : μ ≪ volume) (hc : IsCompact μ.support)
    {r : ℝ} (hr : r ≠ 0) : measureLogConcave (gaussianSmoothing μ r) := by
  rw [gaussianSmoothing_eq_withDensity_of_absolutelyContinuous hAC hc hr]
  exact measureLogConcave_withDensity_of_pointwise
    (gaussianSmoothedDensity_contDiff hc r).continuous.measurable.ennreal_ofReal
    (fun x y _ ht0 ht1 => hμ.gaussianSmoothedDensity_logConcave_of_absolutelyContinuous
      hAC hc hr x y ht0 ht1)

theorem measureLogConcave.tendsto_coordinate_moment_gaussianSmoothing {n : ℕ}
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : measureLogConcave μ)
    {ι : Type*} [Fintype ι] (s : ι → Fin n) :
    Tendsto (fun r : ℝ => ∫ x, ∏ a, x (s a) ∂gaussianSmoothing μ r)
      (𝓝 0) (𝓝 (∫ x, ∏ a, x (s a) ∂μ)) := by
  let d := Fintype.card ι
  let bound : Space n × Space n → ℝ := fun p =>
    2 ^ (d - 1) * (‖p.1‖ ^ d + ‖p.2‖ ^ d)
  have hG := (gaussianExample_isKLSMeasure n).admissibleMeasure.logConcave
  have hb : Integrable bound (μ.prod (gaussianExample n)) :=
    (((hμ.integrable_norm_pow d).comp_fst (gaussianExample n)).add
      ((hG.integrable_norm_pow d).comp_snd μ)).const_mul _
  have hr : ∀ᶠ r : ℝ in 𝓝 0, ‖r‖ ≤ 1 := by
    filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) zero_lt_one] with r hr
    simpa using hr
  have hh := tendsto_integral_filter_of_dominated_convergence
    (μ := μ.prod (gaussianExample n))
    (F := fun r p => ∏ a, (p.1 + r • p.2) (s a))
    (f := fun p => ∏ a, p.1 (s a)) bound
    (Eventually.of_forall fun _ => by fun_prop)
    (hr.mono fun r hr => Eventually.of_forall fun p =>
      coordinate_prod_gaussian_bound s p.1 p.2 hr) hb
    (Eventually.of_forall fun p => by
      have hp : Continuous (fun r : ℝ => ∏ a, (p.1 + r • p.2) (s a)) := by fun_prop
      simpa using hp.tendsto 0)
  have hi : (∫ p : Space n × Space n, ∏ a, p.1 (s a) ∂μ.prod (gaussianExample n)) =
      ∫ x, ∏ a, x (s a) ∂μ := by
    simpa only [probReal_univ, one_smul] using
      (integral_fun_fst (μ := μ) (ν := gaussianExample n) (fun x : Space n => ∏ a, x (s a)))
  simp_rw [← integral_gaussianSmoothing_eq_prod μ _ (f := fun x => ∏ a, x (s a)) (by fun_prop)] at hh
  simpa only [hi] using hh

theorem measureLogConcave.tendsto_matrixQuadratic_gaussianSmoothing
    {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hμ : measureLogConcave μ) (hAC : μ ≪ volume) (hc : IsCompact μ.support)
    (M : Matrix (Fin n) (Fin n) ℝ) :
    Tendsto (fun k => ∫ x, matrixQuadratic M x ∂gaussianSmoothing μ (cutoffScale k))
      atTop (𝓝 (∫ x, matrixQuadratic M x ∂μ)) := by
  have heq (k : ℕ) : (∫ x, matrixQuadratic M x ∂gaussianSmoothing μ (cutoffScale k)) =
      ∑ i, ∑ j, M i j * ∫ x : Space n, x i * x j ∂gaussianSmoothing μ (cutoffScale k) :=
    (hμ.gaussianSmoothing_of_absolutelyContinuous hAC hc (cutoffScale_pos k).ne').integral_matrixQuadratic_sum M
  simp_rw [heq, hμ.integral_matrixQuadratic_sum M]
  apply tendsto_finsetSum
  intro i _
  apply tendsto_finsetSum
  intro j _
  apply Tendsto.const_mul
  simpa [Fin.prod_univ_succ, Function.comp_def] using
    (hμ.tendsto_coordinate_moment_gaussianSmoothing ![i, j]).comp cutoffScale_tendsto_zero

theorem measureLogConcave.tendsto_matrixQuadratic_sq_gaussianSmoothing
    {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hμ : measureLogConcave μ) (hAC : μ ≪ volume) (hc : IsCompact μ.support)
    (M : Matrix (Fin n) (Fin n) ℝ) :
    Tendsto (fun k => ∫ x, matrixQuadratic M x ^ 2 ∂gaussianSmoothing μ (cutoffScale k))
      atTop (𝓝 (∫ x, matrixQuadratic M x ^ 2 ∂μ)) := by
  have heq (k : ℕ) : (∫ x, matrixQuadratic M x ^ 2 ∂gaussianSmoothing μ (cutoffScale k)) =
      ∑ i, ∑ j, ∑ a, ∑ b, (M i j * M a b) *
        ∫ x : Space n, x i * x j * x a * x b ∂gaussianSmoothing μ (cutoffScale k) :=
    (hμ.gaussianSmoothing_of_absolutelyContinuous hAC hc (cutoffScale_pos k).ne').integral_matrixQuadratic_sq_sum M
  simp_rw [heq, hμ.integral_matrixQuadratic_sq_sum M]
  apply tendsto_finsetSum
  intro i _
  apply tendsto_finsetSum
  intro j _
  apply tendsto_finsetSum
  intro a _
  apply tendsto_finsetSum
  intro b _
  apply Tendsto.const_mul
  simpa [Fin.prod_univ_succ, mul_assoc, Function.comp_def] using
    (hμ.tendsto_coordinate_moment_gaussianSmoothing ![i, j, a, b]).comp cutoffScale_tendsto_zero

theorem measureLogConcave.tendsto_quadraticVariance_gaussianSmoothing
    {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hμ : measureLogConcave μ) (hAC : μ ≪ volume) (hc : IsCompact μ.support)
    (M : Matrix (Fin n) (Fin n) ℝ) :
    Tendsto (fun k => ProbabilityTheory.variance (matrixQuadratic M)
      (gaussianSmoothing μ (cutoffScale k)))
      atTop (𝓝 (ProbabilityTheory.variance (matrixQuadratic M) μ)) := by
  have heq (k : ℕ) : ProbabilityTheory.variance (matrixQuadratic M)
      (gaussianSmoothing μ (cutoffScale k)) =
      (∫ x, matrixQuadratic M x ^ 2 ∂gaussianSmoothing μ (cutoffScale k)) -
        (∫ x, matrixQuadratic M x ∂gaussianSmoothing μ (cutoffScale k)) ^ 2 :=
    ProbabilityTheory.variance_eq_sub
      ((hμ.gaussianSmoothing_of_absolutelyContinuous hAC hc
        (cutoffScale_pos k).ne').memLp_two_matrixQuadratic M)
  have hh := (hμ.tendsto_matrixQuadratic_sq_gaussianSmoothing hAC hc M).sub
    ((hμ.tendsto_matrixQuadratic_gaussianSmoothing hAC hc M).pow 2)
  simpa only [heq, ProbabilityTheory.variance_eq_sub (hμ.memLp_two_matrixQuadratic M),
    Pi.pow_apply] using hh

end KLS
end

#print axioms KLS.gaussianSmoothing_eq_potentialMeasure_of_absolutelyContinuous
#print axioms KLS.measureLogConcave.gaussianSmoothedPotential_convex_of_absolutelyContinuous
#print axioms KLS.measureLogConcave.tendsto_coordinate_moment_gaussianSmoothing
#print axioms KLS.measureLogConcave.tendsto_quadraticVariance_gaussianSmoothing

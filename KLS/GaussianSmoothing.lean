import KLS.GaussianExample
import KLS.LogConcavityConvolution
import KLS.CompactKernelSmoothing
import KLS.LogConcavityDensityRegularity

/-!
# Actual scaled Gaussian kernels and convolution smoothing

The law is the actual scalar pushforward of the standard Gaussian. Its
explicit positive smooth density includes the change-of-variables factor.
Convolving this law with a log-concave density preserves compact-set
log-concavity. For a compactly supported probability input, the resulting
density is a strictly positive smooth integral of the actual Gaussian kernel.
-/

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped ENNReal MeasureTheory ContDiff Topology

noncomputable section
namespace KLS

def scaledGaussianMeasure (n : ℕ) (r : ℝ) : Measure (Space n) :=
  (gaussianExample n).map (fun x => r • x)

def scaledGaussianKernel (n : ℕ) (r : ℝ) (x : Space n) : ℝ :=
  |(r ^ n)⁻¹| * Real.exp (-gaussianPotential n (r⁻¹ • x))

def gaussianSmoothing {n : ℕ} (μ : Measure (Space n)) (r : ℝ) : Measure (Space n) :=
  μ ∗ scaledGaussianMeasure n r

def gaussianSmoothedDensity {n : ℕ} (μ : Measure (Space n)) (r : ℝ) (x : Space n) : ℝ :=
  ∫ y, scaledGaussianKernel n r (x - y) ∂μ

instance scaledGaussianMeasure_isProbability (n : ℕ) (r : ℝ) :
    IsProbabilityMeasure (scaledGaussianMeasure n r) := by
  unfold scaledGaussianMeasure
  infer_instance

instance gaussianSmoothing_isProbability {n : ℕ} (μ : Measure (Space n))
    [IsProbabilityMeasure μ] (r : ℝ) : IsProbabilityMeasure (gaussianSmoothing μ r) := by
  unfold gaussianSmoothing
  infer_instance

lemma scaledGaussianKernel_pos {n : ℕ} {r : ℝ} (hr : r ≠ 0) (x : Space n) :
    0 < scaledGaussianKernel n r x := by
  unfold scaledGaussianKernel
  exact mul_pos (abs_pos.mpr (inv_ne_zero (pow_ne_zero n hr))) (Real.exp_pos _)

lemma scaledGaussianKernel_contDiff (n : ℕ) (r : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (scaledGaussianKernel n r) := by
  unfold scaledGaussianKernel gaussianPotential gaussianCoordinatePotential
  fun_prop

lemma scaledGaussianMeasure_eq_withDensity {n : ℕ} {r : ℝ} (hr : r ≠ 0) :
    scaledGaussianMeasure n r = (volume : Measure (Space n)).withDensity
      (fun x => ENNReal.ofReal (scaledGaussianKernel n r x)) := by
  let e : Space n ≃ᵐ Space n := (Homeomorph.smulOfNeZero r hr).toMeasurableEquiv
  have hd : gaussianExample n = (volume : Measure (Space n)).withDensity
      (fun x => ENNReal.ofReal (Real.exp (-gaussianPotential n x))) := by
    rw [gaussianExample_eq_withDensity_prod, ← gaussianPotential_exp_density]
    rfl
  rw [scaledGaussianMeasure, hd]
  change ((volume : Measure (Space n)).withDensity
    (fun x => ENNReal.ofReal (Real.exp (-gaussianPotential n x)))).map e = _
  rw [map_withDensity_measurableEquiv e _ _ (by
    unfold gaussianPotential gaussianCoordinatePotential
    fun_prop)]
  have he : (volume : Measure (Space n)).map e =
      ENNReal.ofReal |(r ^ n)⁻¹| • (volume : Measure (Space n)) := by
    have hefun : (e : Space n → Space n) = fun x => r • x := by
      ext x
      simp [e, Homeomorph.smulOfNeZero, Homeomorph.smul, Units.smul_def]
    rw [hefun]
    simpa only [finrank_euclideanSpace, Fintype.card_fin]
      using Measure.map_addHaar_smul (volume : Measure (Space n)) hr
  rw [he, withDensity_smul_measure, ← withDensity_smul _ (by
    unfold gaussianPotential gaussianCoordinatePotential
    fun_prop)]
  congr 1
  funext x
  change ENNReal.ofReal |(r ^ n)⁻¹| *
    ENNReal.ofReal (Real.exp (-gaussianPotential n (r⁻¹ • x))) = _
  rw [← ENNReal.ofReal_mul (abs_nonneg _)]
  rfl

lemma scaledGaussianKernel_logConcave {n : ℕ} {r : ℝ} (hr : r ≠ 0)
    (x y : Space n) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ENNReal.ofReal (scaledGaussianKernel n r x) ^ t *
      ENNReal.ofReal (scaledGaussianKernel n r y) ^ (1 - t) ≤
        ENNReal.ofReal (scaledGaussianKernel n r (t • x + (1 - t) • y)) := by
  have hc : 0 < |(r ^ n)⁻¹| := abs_pos.mpr (inv_ne_zero (pow_ne_zero n hr))
  let V : Space n → ℝ := fun z => gaussianPotential n (r⁻¹ • z) - Real.log |(r ^ n)⁻¹|
  have hv : ConvexOn ℝ univ V := by
    have hh : ConvexOn ℝ univ (fun z : Space n => gaussianPotential n (r⁻¹ • z)) := by
      refine ⟨convex_univ, ?_⟩
      intro z _ w _ a b ha hb hab
      simpa only [smul_add, smul_smul, mul_comm r⁻¹] using
        (gaussianPotential_convex n).2 (mem_univ (r⁻¹ • z)) (mem_univ (r⁻¹ • w)) ha hb hab
    convert hh.add_const (-Real.log |(r ^ n)⁻¹|) using 1
  have hv' : ExtendedConvex (fun z => (V z : WithTop ℝ)) := by
    simpa [ExtendedConvex] using hv.convex_epigraph
  have he (z : Space n) : expNegPotential (V z : WithTop ℝ) =
      ENNReal.ofReal (scaledGaussianKernel n r z) := by
    change ENNReal.ofReal (Real.exp (-V z)) = _
    dsimp [V, scaledGaussianKernel]
    rw [neg_sub, Real.exp_sub, Real.exp_log hc]
    congr 1
    rw [div_eq_mul_inv, Real.exp_neg]
  simpa only [he] using hv'.expNegPotential_logConcave x y ht0 ht1

theorem HasLogConcaveDensity.gaussianSmoothing_logConcave {n : ℕ}
    {μ : Measure (Space n)} (hμ : HasLogConcaveDensity μ) {r : ℝ} (hr : r ≠ 0) :
    KLS.measureLogConcave (gaussianSmoothing μ r) := by
  obtain ⟨V, hv, hm, hrepr⟩ := hμ
  rw [gaussianSmoothing, hrepr, scaledGaussianMeasure_eq_withDensity hr]
  exact measureLogConcave_conv_withDensity hm
    (scaledGaussianKernel_contDiff n r).continuous.measurable.ennreal_ofReal
    (fun x y _ ht0 ht1 => hv.expNegPotential_logConcave x y ht0 ht1)
    (fun x y _ ht0 ht1 => scaledGaussianKernel_logConcave hr x y ht0 ht1)

theorem admissibleMeasure.gaussianSmoothing_logConcave {n : ℕ}
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ) {r : ℝ} (hr : r ≠ 0) :
    KLS.measureLogConcave (gaussianSmoothing μ r) :=
  hμ.hasLogConcaveDensity.gaussianSmoothing_logConcave hr

theorem gaussianSmoothedDensity_contDiff {n : ℕ} {μ : Measure (Space n)}
    [IsFiniteMeasure μ] (hμ : IsCompact μ.support) (r : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (gaussianSmoothedDensity μ r) :=
  contDiff_integral_translate_of_compact_support hμ (scaledGaussianKernel_contDiff n r)

lemma integrable_scaledGaussianKernel_translate {n : ℕ} {μ : Measure (Space n)}
    [IsFiniteMeasure μ] (hμ : IsCompact μ.support) (r : ℝ) (x : Space n) :
    Integrable (fun y => scaledGaussianKernel n r (x - y)) μ :=
  integrable_of_continuous_compact_support_measure hμ
    ((scaledGaussianKernel_contDiff n r).continuous.comp (continuous_const.sub continuous_id))

theorem gaussianSmoothedDensity_pos {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : IsCompact μ.support) {r : ℝ} (hr : r ≠ 0)
    (x : Space n) : 0 < gaussianSmoothedDensity μ r x := by
  unfold gaussianSmoothedDensity
  rw [integral_pos_iff_support_of_nonneg
    (fun y => (scaledGaussianKernel_pos hr (x - y)).le)
    (integrable_scaledGaussianKernel_translate hμ r x)]
  have hs : Function.support (fun y => scaledGaussianKernel n r (x - y)) = univ := by
    ext y
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (scaledGaussianKernel_pos hr (x - y)).ne'
  simp [hs]

lemma admissibleMeasure.ofReal_gaussianSmoothedDensity {n : ℕ} {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (hc : IsCompact μ.support) {r : ℝ} (hr : r ≠ 0)
    (x : Space n) : ENNReal.ofReal (gaussianSmoothedDensity μ r x) =
      (lowerBallDensity μ ⋆ₗ (fun z => ENNReal.ofReal (scaledGaussianKernel n r z))) x := by
  let : IsProbabilityMeasure μ := hμ.isProb
  rw [gaussianSmoothedDensity,
    ofReal_integral_eq_lintegral_ofReal (integrable_scaledGaussianKernel_translate hc r x)
      (Eventually.of_forall fun y => (scaledGaussianKernel_pos hr (x - y)).le)]
  conv_lhs => rw [hμ.eq_withDensity_lowerBallDensity]
  have hg : Measurable (fun y => ENNReal.ofReal (scaledGaussianKernel n r (x - y))) :=
    ((scaledGaussianKernel_contDiff n r).continuous.measurable.comp
      (measurable_const.sub measurable_id)).ennreal_ofReal
  rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_lowerBallDensity μ) hg]
  simp only [lconvolution, sub_eq_add_neg, add_comm, Pi.mul_apply]

theorem admissibleMeasure.gaussianSmoothing_eq_withDensity {n : ℕ}
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ) (hc : IsCompact μ.support)
    {r : ℝ} (hr : r ≠ 0) : gaussianSmoothing μ r =
      (volume : Measure (Space n)).withDensity
        (fun x => ENNReal.ofReal (gaussianSmoothedDensity μ r x)) := by
  let : IsProbabilityMeasure μ := hμ.isProb
  rw [gaussianSmoothing, scaledGaussianMeasure_eq_withDensity hr]
  conv_lhs => rw [hμ.eq_withDensity_lowerBallDensity]
  rw [conv_withDensity_eq_lconvolution (measurable_lowerBallDensity μ)
    (scaledGaussianKernel_contDiff n r).continuous.measurable.ennreal_ofReal]
  congr 1
  funext x
  exact (hμ.ofReal_gaussianSmoothedDensity hc hr x).symm

theorem admissibleMeasure.gaussianSmoothedDensity_logConcave {n : ℕ}
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ) (hc : IsCompact μ.support)
    {r : ℝ} (hr : r ≠ 0) (x y : Space n) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ENNReal.ofReal (gaussianSmoothedDensity μ r x) ^ t *
      ENNReal.ofReal (gaussianSmoothedDensity μ r y) ^ (1 - t) ≤
        ENNReal.ofReal (gaussianSmoothedDensity μ r (t • x + (1 - t) • y)) := by
  let : IsProbabilityMeasure μ := hμ.isProb
  simp_rw [hμ.ofReal_gaussianSmoothedDensity hc hr]
  exact lconvolution_logConcave (measurable_lowerBallDensity μ)
    (scaledGaussianKernel_contDiff n r).continuous.measurable.ennreal_ofReal
    (fun x y _ ht0 ht1 => hμ.logConcave.lowerBallDensity_logConcave x y ht0 ht1)
    (fun x y _ ht0 ht1 => scaledGaussianKernel_logConcave hr x y ht0 ht1) x y ht0 ht1

def gaussianSmoothedPotential {n : ℕ} (μ : Measure (Space n)) (r : ℝ) (x : Space n) : ℝ :=
  -Real.log (gaussianSmoothedDensity μ r x)

theorem gaussianSmoothedPotential_contDiff {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hc : IsCompact μ.support) {r : ℝ} (hr : r ≠ 0) :
    ContDiff ℝ (⊤ : ℕ∞) (gaussianSmoothedPotential μ r) := by
  exact ((gaussianSmoothedDensity_contDiff hc r).log
    (fun x => (gaussianSmoothedDensity_pos hc hr x).ne')).neg

theorem admissibleMeasure.gaussianSmoothedPotential_convex {n : ℕ}
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ) (hc : IsCompact μ.support)
    {r : ℝ} (hr : r ≠ 0) : ConvexOn ℝ univ (gaussianSmoothedPotential μ r) := by
  let : IsProbabilityMeasure μ := hμ.isProb
  have hh := convexOn_realDensityPotential
    (d := fun x => ENNReal.ofReal (gaussianSmoothedDensity μ r x))
    (fun x => ENNReal.ofReal_lt_top)
    (fun x y _ ht0 ht1 => hμ.gaussianSmoothedDensity_logConcave hc hr x y ht0 ht1)
  have hs : {x | 0 < ENNReal.ofReal (gaussianSmoothedDensity μ r x)} = univ := by
    ext x
    simp only [mem_ofPred_eq, mem_univ, iff_true, ENNReal.ofReal_pos]
    exact gaussianSmoothedDensity_pos hc hr x
  rw [hs] at hh
  convert hh using 1
  ext x
  simp only [realDensityPotential, ENNReal.toReal_ofReal
    (gaussianSmoothedDensity_pos hc hr x).le, gaussianSmoothedPotential]

theorem admissibleMeasure.gaussianSmoothing_eq_exp_potential {n : ℕ}
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ) (hc : IsCompact μ.support)
    {r : ℝ} (hr : r ≠ 0) : gaussianSmoothing μ r =
      (volume : Measure (Space n)).withDensity
        (fun x => ENNReal.ofReal (Real.exp (-gaussianSmoothedPotential μ r x))) := by
  let : IsProbabilityMeasure μ := hμ.isProb
  rw [hμ.gaussianSmoothing_eq_withDensity hc hr]
  congr 1
  funext x
  rw [gaussianSmoothedPotential, neg_neg, Real.exp_log (gaussianSmoothedDensity_pos hc hr x)]

end KLS
end

#print axioms KLS.scaledGaussianMeasure_eq_withDensity
#print axioms KLS.admissibleMeasure.gaussianSmoothing_logConcave
#print axioms KLS.gaussianSmoothedDensity_contDiff
#print axioms KLS.gaussianSmoothedDensity_pos
#print axioms KLS.admissibleMeasure.gaussianSmoothedPotential_convex
#print axioms KLS.admissibleMeasure.gaussianSmoothing_eq_exp_potential

import KLS.GaussianSmoothingMoments

/-!
# Exact isotropic normalization of Gaussian smoothing

The actual law of `(X+rG)/sqrt(1+r²)` is probability, log-concave, and isotropic
when X is admissible and G is an independent standard Gaussian. All first and
second moments are obtained from the fixed product measure, including their
integrability.
-/

open MeasureTheory ProbabilityTheory Set Filter Metric ContinuousLinearMap
open scoped ENNReal MeasureTheory ContDiff Topology BigOperators

noncomputable section
namespace KLS

def gaussianNormalization (r : ℝ) : ℝ := (Real.sqrt (1 + r ^ 2))⁻¹

def isotropicGaussianSmoothing {n : ℕ} (μ : Measure (Space n)) (r : ℝ) : Measure (Space n) :=
  (gaussianSmoothing μ r).map (fun x => gaussianNormalization r • x)

lemma gaussianNormalization_pos (r : ℝ) : 0 < gaussianNormalization r := by
  unfold gaussianNormalization
  positivity

lemma gaussianNormalization_sq_mul (r : ℝ) :
    gaussianNormalization r ^ 2 * (1 + r ^ 2) = 1 := by
  have hp : 0 < 1 + r ^ 2 := by positivity
  simp [gaussianNormalization, inv_pow, Real.sq_sqrt hp.le, hp.ne']

lemma gaussianNormalization_tendsto : Tendsto gaussianNormalization (𝓝 0) (𝓝 1) := by
  have hh : ContinuousAt gaussianNormalization 0 := by
    unfold gaussianNormalization
    apply ContinuousAt.inv₀
    · fun_prop
    · norm_num
  simpa [gaussianNormalization] using hh.tendsto

instance isotropicGaussianSmoothing_isProbability {n : ℕ} (μ : Measure (Space n))
    [IsProbabilityMeasure μ] (r : ℝ) :
    IsProbabilityMeasure (KLS.isotropicGaussianSmoothing μ r) := by
  unfold isotropicGaussianSmoothing
  infer_instance

theorem IsIsotropic.memLp_id_gaussianSmoothing {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : IsIsotropic μ) (r : ℝ) :
    MemLp (fun x : Space n => x) 2 (gaussianSmoothing μ r) := by
  rw [gaussianSmoothing_eq_map_prod]
  apply (memLp_map_measure_iff aestronglyMeasurable_id (by fun_prop)).mpr
  exact (hμ.memLp_id.comp_fst (gaussianExample n)).add
    (((gaussianExample_isIsotropic n).memLp_id.comp_snd μ).const_smul r)

lemma IsIsotropic.integral_coordinate_gaussianSmoothing {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : IsIsotropic μ) (r : ℝ) (i : Fin n) :
    (∫ x : Space n, x i ∂gaussianSmoothing μ r) = 0 := by
  rw [integral_gaussianSmoothing_eq_prod μ r (by fun_prop)]
  change (∫ p : Space n × Space n, p.1 i + r * p.2 i ∂μ.prod (gaussianExample n)) = 0
  rw [integral_add ((hμ.integrable_coordinate i).comp_fst (gaussianExample n))
    (((gaussianExample_isIsotropic n).integrable_coordinate i).comp_snd μ |>.const_mul r),
    integral_const_mul]
  rw [integral_fun_fst (fun x : Space n => x i),
    integral_fun_snd (fun x : Space n => x i), hμ.integral_coordinate,
    gaussianExample_integral_coordinate]
  simp

lemma IsIsotropic.integral_coordinate_mul_gaussianSmoothing {n : ℕ}
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : IsIsotropic μ)
    (r : ℝ) (i j : Fin n) :
    (∫ x : Space n, x i * x j ∂gaussianSmoothing μ r) =
      (1 + r ^ 2) * (1 : Matrix (Fin n) (Fin n) ℝ) i j := by
  simp only [Matrix.one_apply]
  have hG := gaussianExample_isIsotropic n
  have hxx := (hμ.2.2.1 i j).comp_fst (gaussianExample n)
  have hxy := ((hμ.integrable_coordinate i).mul_prod (hG.integrable_coordinate j)).const_mul r
  have hyx := ((hμ.integrable_coordinate j).mul_prod (hG.integrable_coordinate i)).const_mul r
  have hyy := ((hG.2.2.1 i j).comp_snd μ).const_mul (r ^ 2)
  rw [integral_gaussianSmoothing_eq_prod μ r (by fun_prop)]
  have he : (fun p : Space n × Space n =>
      (p.1 + r • p.2) i * (p.1 + r • p.2) j) =
      fun p => p.1 i * p.1 j + r * (p.1 i * p.2 j) +
        r * (p.1 j * p.2 i) + r ^ 2 * (p.2 i * p.2 j) := by
    ext p
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  have hs2 : Integrable (fun p : Space n × Space n =>
      p.1 i * p.1 j + r * (p.1 i * p.2 j)) (μ.prod (gaussianExample n)) :=
    hxx.add hxy
  have hs3 : Integrable (fun p : Space n × Space n =>
      p.1 i * p.1 j + r * (p.1 i * p.2 j) + r * (p.1 j * p.2 i))
        (μ.prod (gaussianExample n)) := hs2.add hyx
  rw [he, integral_add hs3 hyy, integral_add hs2 hyx, integral_add hxx hxy]
  simp only [integral_const_mul]
  have hcross (a b : Fin n) :
      (∫ p : Space n × Space n, p.1 a * p.2 b ∂μ.prod (gaussianExample n)) = 0 := by
    rw [integral_prod_mul (fun x : Space n => x a) (fun y : Space n => y b),
      hμ.integral_coordinate, zero_mul]
  have hμij := congrArg (fun M => M i j) hμ.2.2.2
  have hGij := congrArg (fun M => M i j) hG.2.2.2
  change (∫ x : Space n, x i * x j ∂μ) = _ at hμij
  change (∫ x : Space n, x i * x j ∂gaussianExample n) = _ at hGij
  rw [integral_fun_fst (fun x : Space n => x i * x j),
    integral_fun_snd (fun x : Space n => x i * x j),
    hcross i j, hcross j i]
  simp only [probReal_univ, one_smul, hμij, hGij, Matrix.one_apply]
  ring

theorem IsIsotropic.isotropicGaussianSmoothing {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : IsIsotropic μ) (r : ℝ) :
    KLS.IsIsotropic (KLS.isotropicGaussianSmoothing μ r) := by
  have hL2 : MemLp (fun x : Space n => x) 2 (KLS.isotropicGaussianSmoothing μ r) := by
    rw [KLS.isotropicGaussianSmoothing]
    apply (memLp_map_measure_iff aestronglyMeasurable_id (by fun_prop)).mpr
    exact (hμ.memLp_id_gaussianSmoothing r).const_smul (gaussianNormalization r)
  have hcoord (i : Fin n) : MemLp (fun x : Space n => x i) 2
      (KLS.isotropicGaussianSmoothing μ r) := (EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp' hL2
  refine ⟨hL2.integrable (by norm_num), ?_,
    (fun i j => (hcoord i).integrable_mul (hcoord j)), ?_⟩
  · ext i
    have he := (EuclideanSpace.proj (𝕜 := ℝ) i).integral_comp_comm
      (hL2.integrable (by norm_num))
    change (∫ x : Space n, x i ∂KLS.isotropicGaussianSmoothing μ r) =
      (∫ x : Space n, x ∂KLS.isotropicGaussianSmoothing μ r) i at he
    rw [← he, KLS.isotropicGaussianSmoothing, integral_map (by fun_prop) (by fun_prop)]
    change (∫ x : Space n, gaussianNormalization r * x i ∂gaussianSmoothing μ r) = 0
    rw [integral_const_mul, hμ.integral_coordinate_gaussianSmoothing, mul_zero]
  · ext i j
    change (∫ x : Space n, x i * x j ∂KLS.isotropicGaussianSmoothing μ r) = _
    rw [KLS.isotropicGaussianSmoothing, integral_map (by fun_prop) (by fun_prop)]
    have he (x : Space n) : (gaussianNormalization r • x) i * (gaussianNormalization r • x) j =
        gaussianNormalization r ^ 2 * (x i * x j) := by
      simp only [PiLp.smul_apply, smul_eq_mul]
      ring
    simp_rw [he]
    rw [integral_const_mul, hμ.integral_coordinate_mul_gaussianSmoothing,
      ← mul_assoc, gaussianNormalization_sq_mul, one_mul]

theorem admissibleMeasure.isotropicGaussianSmoothing {n : ℕ} {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {r : ℝ} (hr : r ≠ 0) :
    KLS.admissibleMeasure (KLS.isotropicGaussianSmoothing μ r) := by
  let : IsProbabilityMeasure μ := hμ.isProb
  refine ⟨inferInstance, ?_, hμ.isotropic.isotropicGaussianSmoothing r⟩
  let L : Space n →L[ℝ] Space n := gaussianNormalization r • ContinuousLinearMap.id ℝ _
  exact (hμ.gaussianSmoothing_logConcave hr).map_continuousAffineMap L.toContinuousAffineMap

theorem integral_coordinate_moment_isotropicGaussianSmoothing {n : ℕ}
    (μ : Measure (Space n)) (r : ℝ) {ι : Type*} [Fintype ι] (s : ι → Fin n) :
    (∫ x, ∏ a, x (s a) ∂KLS.isotropicGaussianSmoothing μ r) =
      gaussianNormalization r ^ Fintype.card ι *
        ∫ x, ∏ a, x (s a) ∂gaussianSmoothing μ r := by
  rw [KLS.isotropicGaussianSmoothing, integral_map (by fun_prop) (by fun_prop)]
  simp only [PiLp.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, integral_const_mul]

theorem admissibleMeasure.tendsto_coordinate_moment_isotropicGaussianSmoothing {n : ℕ}
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {ι : Type*} [Fintype ι] (s : ι → Fin n) :
    Tendsto (fun r : ℝ => ∫ x, ∏ a, x (s a) ∂KLS.isotropicGaussianSmoothing μ r)
      (𝓝 0) (𝓝 (∫ x, ∏ a, x (s a) ∂μ)) := by
  simp_rw [integral_coordinate_moment_isotropicGaussianSmoothing]
  simpa only [one_pow, one_mul] using (gaussianNormalization_tendsto.pow (Fintype.card ι)).mul
    (hμ.tendsto_coordinate_moment_gaussianSmoothing s)

end KLS
end

#print axioms KLS.IsIsotropic.integral_coordinate_mul_gaussianSmoothing
#print axioms KLS.IsIsotropic.isotropicGaussianSmoothing
#print axioms KLS.admissibleMeasure.isotropicGaussianSmoothing
#print axioms KLS.admissibleMeasure.tendsto_coordinate_moment_isotropicGaussianSmoothing

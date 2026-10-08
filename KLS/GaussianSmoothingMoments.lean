import KLS.GaussianSmoothing
import KLS.WhitenedCutoffMoments

/-!
# Moment convergence of actual Gaussian smoothing

The smoothing is identified with addition on the fixed product probability
space. A bound by a sum of norm moments proves convergence of every finite
coordinate moment as the Gaussian scale tends to zero.
-/

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped ENNReal MeasureTheory Topology BigOperators

noncomputable section
namespace KLS

theorem gaussianSmoothing_eq_map_prod {n : ℕ} (μ : Measure (Space n)) (r : ℝ) :
    gaussianSmoothing μ r =
      (μ.prod (gaussianExample n)).map (fun p => p.1 + r • p.2) := by
  have he : μ.prod ((gaussianExample n).map (fun x => r • x)) =
      (μ.prod (gaussianExample n)).map (fun p => (p.1, r • p.2)) := by
    simpa only [Measure.map_id, Prod.map_def, id_eq] using Measure.map_prod_map μ (gaussianExample n) measurable_id
      (show Measurable (fun x : Space n => r • x) by fun_prop)
  rw [gaussianSmoothing, scaledGaussianMeasure, Measure.conv, he,
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

theorem integral_gaussianSmoothing_eq_prod {n : ℕ} (μ : Measure (Space n)) (r : ℝ)
    {f : Space n → ℝ} (hf : Measurable f) :
    (∫ x, f x ∂gaussianSmoothing μ r) =
      ∫ p, f (p.1 + r • p.2) ∂μ.prod (gaussianExample n) := by
  rw [gaussianSmoothing_eq_map_prod,
    integral_map (by fun_prop) hf.aestronglyMeasurable]

lemma coordinate_prod_gaussian_bound {n : ℕ} {ι : Type*} [Fintype ι]
    (s : ι → Fin n) (x y : Space n) {r : ℝ} (hr : ‖r‖ ≤ 1) :
    ‖∏ a, (x + r • y) (s a)‖ ≤
      2 ^ (Fintype.card ι - 1) * (‖x‖ ^ Fintype.card ι + ‖y‖ ^ Fintype.card ι) := by
  have hv : ‖x + r • y‖ ≤ ‖x‖ + ‖y‖ := by
    calc
      ‖x + r • y‖ ≤ ‖x‖ + ‖r • y‖ := norm_add_le _ _
      _ = ‖x‖ + ‖r‖ * ‖y‖ := by rw [norm_smul]
      _ ≤ ‖x‖ + ‖y‖ := by nlinarith [norm_nonneg y]
  calc
    ‖∏ a, (x + r • y) (s a)‖ = ∏ a, ‖(x + r • y) (s a)‖ := norm_prod _ _
    _ ≤ ∏ _a : ι, (‖x‖ + ‖y‖) :=
      Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        (fun a _ => (PiLp.norm_apply_le (x + r • y) (s a)).trans hv)
    _ = (‖x‖ + ‖y‖) ^ Fintype.card ι := by simp
    _ ≤ _ := add_pow_le (norm_nonneg x) (norm_nonneg y) _

/-- All finite coordinate moments converge, with no compact-support premise. -/
theorem admissibleMeasure.tendsto_coordinate_moment_gaussianSmoothing {n : ℕ}
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {ι : Type*} [Fintype ι] (s : ι → Fin n) :
    Tendsto (fun r : ℝ => ∫ x, ∏ a, x (s a) ∂gaussianSmoothing μ r)
      (𝓝 0) (𝓝 (∫ x, ∏ a, x (s a) ∂μ)) := by
  let : IsProbabilityMeasure μ := hμ.isProb
  let d := Fintype.card ι
  let bound : Space n × Space n → ℝ := fun p =>
    2 ^ (d - 1) * (‖p.1‖ ^ d + ‖p.2‖ ^ d)
  have hG := (gaussianExample_isKLSMeasure n).admissibleMeasure.logConcave
  have hb : Integrable bound (μ.prod (gaussianExample n)) :=
    (((hμ.logConcave.integrable_norm_pow d).comp_fst (gaussianExample n)).add
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

end KLS
end

#print axioms KLS.gaussianSmoothing_eq_map_prod
#print axioms KLS.admissibleMeasure.tendsto_coordinate_moment_gaussianSmoothing

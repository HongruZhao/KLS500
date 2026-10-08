import KLS.SmoothBoundedDensityApproximation
import KLS.StrongConvexAffine
import KLS.TiltDerivatives
import KLS.DensityToClass

/-! Genuine normalized quadratic damping of a compact law. Its integrals
converge to the original ones; a regular bounded density acquires an explicit
positive strong-convexity modulus before covariance whitening. -/

open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped ENNReal Topology ContDiff

noncomputable section
namespace KLS

def quadraticDamping {n : ℕ} (μ : Measure (Space n)) (ε : ℝ) : Measure (Space n) :=
  μ.tilted (fun x => -ε * ‖x‖ ^ 2)

lemma quadraticDamping_zero {n : ℕ} (μ : Measure (Space n)) [IsProbabilityMeasure μ] :
    quadraticDamping μ 0 = μ := by
  simp [quadraticDamping]

lemma isProbabilityMeasure_quadraticDamping {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hc : IsCompact μ.support) (ε : ℝ) :
    IsProbabilityMeasure (quadraticDamping μ ε) :=
  tilted_isProbability_of_compact_support hc (by fun_prop)

lemma support_quadraticDamping {n : ℕ} {μ : Measure (Space n)}
    [IsFiniteMeasure μ] (hc : IsCompact μ.support) (ε : ℝ) :
    (quadraticDamping μ ε).support = μ.support :=
  tilted_support_eq hc (by fun_prop)

lemma integrable_quadraticDamping {n : ℕ} {μ : Measure (Space n)}
    [IsFiniteMeasure μ] (hc : IsCompact μ.support) {f : Space n → ℝ}
    (hf : Integrable f μ) (ε : ℝ) : Integrable f (quadraticDamping μ ε) :=
  integrable_tilted_of_compact_support hc (by fun_prop) hf

/-- Every integrable observable converges, not merely a selected moment. -/
theorem tendsto_integral_quadraticDamping {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hc : IsCompact μ.support) {f : Space n → ℝ}
    (hf : Integrable f μ) :
    Tendsto (fun ε => ∫ x, f x ∂quadraticDamping μ ε) (𝓝 0) (𝓝 (∫ x, f x ∂μ)) := by
  have hh := (hasDerivAt_tiltAverage hc (q := fun _ => 0) (s := fun x => -‖x‖ ^ 2)
    continuous_const (by fun_prop) hf 0).continuousAt.tendsto
  simpa only [tiltAverage, quadraticDamping, zero_add, zero_mul, neg_mul, mul_neg, tilted_const] using hh

lemma HasSmoothBoundedConvexDensity.isCompact_support {n : ℕ} {μ : Measure (Space n)}
    (hμ : HasSmoothBoundedConvexDensity μ) : IsCompact μ.support := by
  obtain ⟨K, V, _, _, hK, _, _, _, rfl⟩ := hμ
  exact hK.isCompact_closure.of_isClosed_subset Measure.isClosed_support
    (fun _ hx => (Measure.support_restrict_subset hx).1)

lemma measureLogConcave_potentialMeasure {n : ℕ} {V : Space n → ℝ}
    (hm : Measurable V) (hc : ConvexOn ℝ univ V) :
    measureLogConcave (potentialMeasure V) := by
  apply measureLogConcave_withDensity_of_pointwise (by fun_prop)
  intro x y t ht ht1
  have hh := hc.2 (mem_univ x) (mem_univ y) ht.le (sub_pos.mpr ht1).le (by ring)
  rw [← exp_neg_affine_eq_geometric (V x) (V y) t (1 - t) ht.le (sub_pos.mpr ht1).le]
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by simpa only [smul_eq_mul] using neg_le_neg hh))

lemma measureLogConcave_restrict_potentialMeasure {n : ℕ} {V : Space n → ℝ}
    (hm : Measurable V) (hc : ConvexOn ℝ univ V) {K : Set (Space n)}
    (hK : MeasurableSet K) (hconv : Convex ℝ K) :
    measureLogConcave ((potentialMeasure V).restrict K) := by
  rw [potentialMeasure, restrict_withDensity hK, ← withDensity_indicator hK]
  apply measureLogConcave_withDensity_of_pointwise
    ((show Measurable (fun x => ENNReal.ofReal (Real.exp (-V x))) by fun_prop).indicator hK)
  intro x y t ht ht1
  by_cases hx : x ∈ K
  · by_cases hy : y ∈ K
    · have hz := hconv hx hy ht.le (sub_pos.mpr ht1).le (by ring)
      simp only [indicator_of_mem hx, indicator_of_mem hy, indicator_of_mem hz]
      have hh := hc.2 (mem_univ x) (mem_univ y) ht.le (sub_pos.mpr ht1).le (by ring)
      rw [← exp_neg_affine_eq_geometric (V x) (V y) t (1 - t) ht.le (sub_pos.mpr ht1).le]
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
        (by simpa only [smul_eq_mul] using neg_le_neg hh))
    · simp only [indicator_of_notMem hy, ENNReal.zero_rpow_of_pos (sub_pos.mpr ht1), mul_zero]
      exact zero_le
  · simp only [indicator_of_notMem hx, ENNReal.zero_rpow_of_pos ht, zero_mul]
    exact zero_le

def dampedPotential {n : ℕ} (μ : Measure (Space n)) (V : Space n → ℝ) (ε : ℝ)
    (x : Space n) : ℝ :=
  V x + ε * ‖x‖ ^ 2 + Real.log (tiltPartition μ (fun y => -ε * ‖y‖ ^ 2))

lemma quadraticDamping_eq_restrict_potentialMeasure {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hs : IsCompact μ.support) {V : Space n → ℝ}
    (hm : Measurable V) {K : Set (Space n)} (hK : MeasurableSet K)
    (heq : μ = (potentialMeasure V).restrict K) (ε : ℝ) :
    quadraticDamping μ ε = (potentialMeasure (dampedPotential μ V ε)).restrict K := by
  have hp : 0 < tiltPartition μ (fun y => -ε * ‖y‖ ^ 2) := tiltPartition_pos hs (by fun_prop)
  rw [quadraticDamping, tilted_eq_normalized_density]
  nth_rw 1 [heq]
  rw [potentialMeasure,
    restrict_withDensity hK, ← withDensity_mul _ (by fun_prop) (by fun_prop),
    potentialMeasure, restrict_withDensity hK]
  congr 1
  funext x
  simp only [Pi.mul_apply, ← ENNReal.ofReal_mul (Real.exp_nonneg _)]
  congr 1
  dsimp [dampedPotential]
  rw [show -(V x + ε * ‖x‖ ^ 2 + Real.log (tiltPartition μ (fun y => -ε * ‖y‖ ^ 2))) =
      -V x + (-ε * ‖x‖ ^ 2) - Real.log (tiltPartition μ (fun y => -ε * ‖y‖ ^ 2)) by ring,
    Real.exp_sub, Real.exp_add, Real.exp_log hp]
  ring

lemma dampedPotential_contDiff {n : ℕ} {μ : Measure (Space n)} {V : Space n → ℝ}
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (ε : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (dampedPotential μ V ε) := by
  unfold dampedPotential
  have hh : ContDiff ℝ (⊤ : ℕ∞) (fun x : Space n => ‖x‖ ^ 2) := contDiff_norm_sq ℝ
  exact (hV.add (contDiff_const.mul hh)).add contDiff_const

lemma dampedPotential_strongConvex {n : ℕ} {μ : Measure (Space n)} {V : Space n → ℝ}
    (hV : ConvexOn ℝ univ V) (ε : ℝ) :
    StrongConvexOn univ (2 * ε) (dampedPotential μ V ε) :=
  strongConvexOn_add_const (strongConvexOn_add_norm_sq hV ε) _

end KLS
end

#print axioms KLS.tendsto_integral_quadraticDamping
#print axioms KLS.quadraticDamping_eq_restrict_potentialMeasure

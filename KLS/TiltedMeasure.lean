import KLS.CompactKernelSmoothing
import Mathlib.MeasureTheory.Measure.Tilted

/-!
# Actual normalized exponential tilts on compact support

The probability law is Mathlib's `Measure.tilted`, with its explicit normalized
Radon--Nikodym density. Compact support discharges exponential integrability
and every continuous multiplier bound. No log-concavity or moment identities
are assumed in these analytic facts.
-/

open MeasureTheory Set Filter
open scoped Topology

noncomputable section
namespace KLS

def tiltPartition {n : ℕ} (μ : Measure (Space n)) (q : Space n → ℝ) : ℝ :=
  ∫ x, Real.exp (q x) ∂μ

def tiltAverage {n : ℕ} (μ : Measure (Space n)) (q f : Space n → ℝ) : ℝ :=
  ∫ x, f x ∂(μ.tilted q)

def exponentialTilt {n : ℕ} (μ : Measure (Space n)) (z : Space n) : Measure (Space n) :=
  μ.tilted (fun x => inner ℝ z x)

theorem integrable_mul_continuous_of_compact_support {n : ℕ}
    {μ : Measure (Space n)} (hμ : IsCompact μ.support)
    {f g : Space n → ℝ} (hf : Integrable f μ) (hg : Continuous g) :
    Integrable (fun x => f x * g x) μ := by
  obtain ⟨C, hC⟩ := hμ.exists_bound_of_continuousOn hg.continuousOn
  apply hf.mul_bdd hg.aestronglyMeasurable
  filter_upwards [μ.support_mem_ae] with x hx using hC x hx

theorem integrable_exp_of_compact_support {n : ℕ}
    {μ : Measure (Space n)} [IsFiniteMeasure μ] (hμ : IsCompact μ.support)
    {q : Space n → ℝ} (hq : Continuous q) :
    Integrable (fun x => Real.exp (q x)) μ :=
  integrable_of_continuous_compact_support_measure hμ (by fun_prop)

theorem tiltPartition_pos {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : IsCompact μ.support)
    {q : Space n → ℝ} (hq : Continuous q) : 0 < tiltPartition μ q :=
  integral_exp_pos (integrable_exp_of_compact_support hμ hq)

theorem tilted_isProbability_of_compact_support {n : ℕ}
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : IsCompact μ.support)
    {q : Space n → ℝ} (hq : Continuous q) : IsProbabilityMeasure (μ.tilted q) :=
  isProbabilityMeasure_tilted (integrable_exp_of_compact_support hμ hq)

theorem tilted_support_eq {n : ℕ} {μ : Measure (Space n)}
    [IsFiniteMeasure μ] (hμ : IsCompact μ.support)
    {q : Space n → ℝ} (hq : Continuous q) : (μ.tilted q).support = μ.support :=
  Set.Subset.antisymm (tilted_absolutelyContinuous μ q).support_mono
    (absolutelyContinuous_tilted (integrable_exp_of_compact_support hμ hq)).support_mono

theorem integrable_tilted_of_compact_support {n : ℕ}
    {μ : Measure (Space n)} [IsFiniteMeasure μ] (hμ : IsCompact μ.support)
    {q f : Space n → ℝ} (hq : Continuous q) (hf : Integrable f μ) :
    Integrable f (μ.tilted q) := by
  rw [integrable_tilted_iff (integrable_exp_of_compact_support hμ hq)]
  simpa only [smul_eq_mul, mul_comm] using
    integrable_mul_continuous_of_compact_support hμ hf (g := fun x => Real.exp (q x))
      (by fun_prop)

theorem integrable_tilted_iff_of_compact_support {n : ℕ}
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : IsCompact μ.support)
    {q f : Space n → ℝ} (hq : Continuous q) :
    Integrable f (μ.tilted q) ↔ Integrable f μ := by
  refine ⟨fun hf => ?_, integrable_tilted_of_compact_support hμ hq⟩
  haveI := tilted_isProbability_of_compact_support hμ hq
  have hc : IsCompact (μ.tilted q).support := by rwa [tilted_support_eq hμ hq]
  have hh := integrable_tilted_of_compact_support hc hq.neg hf
  simpa only [tilted_neg_same (integrable_exp_of_compact_support hμ hq)] using hh

theorem tiltAverage_eq_ratio {n : ℕ} (μ : Measure (Space n))
    (q f : Space n → ℝ) :
    tiltAverage μ q f = (∫ x, f x * Real.exp (q x) ∂μ) / tiltPartition μ q := by
  rw [tiltAverage, integral_tilted]
  simp only [smul_eq_mul, tiltPartition]
  simp_rw [div_mul_eq_mul_div, mul_comm (Real.exp _) (f _)]
  simp_rw [div_eq_mul_inv]
  exact integral_mul_const _ _

theorem tilted_eq_normalized_density {n : ℕ} (μ : Measure (Space n))
    (q : Space n → ℝ) :
    μ.tilted q = μ.withDensity (fun x =>
      ENNReal.ofReal (Real.exp (q x) / tiltPartition μ q)) := rfl

theorem exponentialTilt_isProbability {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : IsCompact μ.support) (z : Space n) :
    IsProbabilityMeasure (exponentialTilt μ z) :=
  tilted_isProbability_of_compact_support hμ (by fun_prop)

theorem exponentialTilt_add {n : ℕ} {μ : Measure (Space n)}
    [IsFiniteMeasure μ] (hμ : IsCompact μ.support) (z w : Space n) :
    exponentialTilt (exponentialTilt μ z) w = exponentialTilt μ (z + w) := by
  rw [exponentialTilt, exponentialTilt,
    tilted_tilted (integrable_exp_of_compact_support hμ (by fun_prop))]
  congr 1
  funext x
  simp [inner_add_left]

end KLS
end

#print axioms KLS.tilted_isProbability_of_compact_support
#print axioms KLS.integrable_tilted_iff_of_compact_support
#print axioms KLS.tiltAverage_eq_ratio
#print axioms KLS.exponentialTilt_add

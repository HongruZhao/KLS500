import KLS.TiltedMeasure
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Differentiating actual exponential tilt averages

Compact support supplies a uniform local bound for the exponential derivative.
The observable itself need only be integrable, and need not be continuous or
bounded. Every differentiation under the integral is proved by domination.
-/

open MeasureTheory Set Filter Metric
open scoped Topology

noncomputable section
namespace KLS

theorem hasDerivAt_integral_exponential_tilt {n : ℕ}
    {μ : Measure (Space n)} (hμ : IsCompact μ.support)
    {q s f : Space n → ℝ} (hq : Continuous q) (hs : Continuous s)
    (hf : Integrable f μ) (t : ℝ) :
    HasDerivAt (fun u : ℝ => ∫ x, f x * Real.exp (q x + u * s x) ∂μ)
      (∫ x, f x * s x * Real.exp (q x + t * s x) ∂μ) t := by
  let D : ℝ × Space n → ℝ := fun p => s p.2 * Real.exp (q p.2 + p.1 * s p.2)
  have hD : Continuous D := by dsimp [D]; fun_prop
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := t - 1) (b := t + 1)).prod hμ
    |>.exists_bound_of_continuousOn hD.continuousOn
  have hfi (u : ℝ) : Integrable (fun x => f x * Real.exp (q x + u * s x)) μ :=
    integrable_mul_continuous_of_compact_support hμ hf (by fun_prop)
  have hfdi (u : ℝ) : Integrable (fun x => f x * s x * Real.exp (q x + u * s x)) μ := by
    simpa only [mul_assoc] using integrable_mul_continuous_of_compact_support hμ hf
      (g := fun x => s x * Real.exp (q x + u * s x)) (by fun_prop)
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F' := fun u x => f x * s x * Real.exp (q x + u * s x))
    (s := Ioo (t - 1) (t + 1)) (bound := fun x => ‖f x‖ * C)
    (Ioo_mem_nhds (by linarith) (by linarith))
    (Eventually.of_forall (fun u => (hfi u).aestronglyMeasurable))
    (hfi t) (hfdi t).aestronglyMeasurable ?_ (hf.norm.mul_const C) ?_).2
  · filter_upwards [μ.support_mem_ae] with x hx
    intro u hu
    rw [mul_assoc, norm_mul]
    exact mul_le_mul_of_nonneg_left (hC (u, x) ⟨⟨hu.1.le, hu.2.le⟩, hx⟩)
      (norm_nonneg _)
  · exact Eventually.of_forall fun x u _ => by
      simpa only [id_eq, mul_comm, mul_left_comm, mul_assoc, one_mul, mul_one] using
        ((((hasDerivAt_id u).mul_const (s x)).const_add (q x)).exp).const_mul (f x)

theorem hasDerivAt_tiltPartition {n : ℕ} {μ : Measure (Space n)}
    [IsFiniteMeasure μ] (hμ : IsCompact μ.support)
    {q s : Space n → ℝ} (hq : Continuous q) (hs : Continuous s) (t : ℝ) :
    HasDerivAt (fun u : ℝ => tiltPartition μ (fun x => q x + u * s x))
      (∫ x, s x * Real.exp (q x + t * s x) ∂μ) t := by
  simpa only [one_mul, tiltPartition] using
    hasDerivAt_integral_exponential_tilt hμ hq hs (integrable_const (1 : ℝ)) t

/-- The derivative of any integrable observable is its tilted covariance with
the score. Both terms are actual expectations under the normalized law. -/
theorem hasDerivAt_tiltAverage {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : IsCompact μ.support)
    {q s f : Space n → ℝ} (hq : Continuous q) (hs : Continuous s)
    (hf : Integrable f μ) (t : ℝ) :
    HasDerivAt (fun u : ℝ => tiltAverage μ (fun x => q x + u * s x) f)
      (tiltAverage μ (fun x => q x + t * s x) (fun x => f x * s x) -
        tiltAverage μ (fun x => q x + t * s x) f *
        tiltAverage μ (fun x => q x + t * s x) s) t := by
  have hp : tiltPartition μ (fun x => q x + t * s x) ≠ 0 :=
    (tiltPartition_pos hμ (by fun_prop)).ne'
  have hd := (hasDerivAt_integral_exponential_tilt hμ hq hs hf t).div
    (hasDerivAt_tiltPartition hμ hq hs t) hp
  simp_rw [tiltAverage_eq_ratio]
  convert hd using 1
  field_simp [hp]
  simp only [mul_comm]

theorem hasDerivAt_log_tiltPartition {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : IsCompact μ.support)
    {q s : Space n → ℝ} (hq : Continuous q) (hs : Continuous s) (t : ℝ) :
    HasDerivAt (fun u : ℝ => Real.log (tiltPartition μ (fun x => q x + u * s x)))
      (tiltAverage μ (fun x => q x + t * s x) s) t := by
  rw [tiltAverage_eq_ratio]
  exact (hasDerivAt_tiltPartition hμ hq hs t).log (tiltPartition_pos hμ (by fun_prop)).ne'

theorem hasDerivAt_exponentialTilt_average {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : IsCompact μ.support)
    {f : Space n → ℝ} (hf : Integrable f μ) (z v : Space n) (t : ℝ) :
    HasDerivAt (fun u : ℝ => ∫ x, f x ∂(exponentialTilt μ (z + u • v)))
      ((∫ x, f x * inner ℝ v x ∂(exponentialTilt μ (z + t • v))) -
        (∫ x, f x ∂(exponentialTilt μ (z + t • v))) *
        (∫ x, inner ℝ v x ∂(exponentialTilt μ (z + t • v)))) t := by
  simpa only [tiltAverage, exponentialTilt, inner_add_left, inner_smul_left,
    RCLike.conj_to_real] using
    hasDerivAt_tiltAverage hμ (q := fun x => inner ℝ z x)
      (s := fun x => inner ℝ v x) (by fun_prop) (by fun_prop) hf t

end KLS
end

#print axioms KLS.hasDerivAt_integral_exponential_tilt
#print axioms KLS.hasDerivAt_tiltAverage
#print axioms KLS.hasDerivAt_log_tiltPartition
#print axioms KLS.hasDerivAt_exponentialTilt_average

import KLS.TiltDerivatives

/-!
# The all-order deterministic moment hierarchy

Every derivative of the unnormalized tilt numerator is an actual integral.
This holds for arbitrary integrable observables on compact support. The
normalized moment hierarchy follows from the proved quotient rule.
-/

open MeasureTheory Set Filter
open scoped Topology BigOperators

noncomputable section
namespace KLS

theorem iteratedDeriv_integral_exponential_tilt {n : ℕ}
    {μ : Measure (Space n)} (hμ : IsCompact μ.support)
    {q s f : Space n → ℝ} (hq : Continuous q) (hs : Continuous s)
    (hf : Integrable f μ) (k : ℕ) (t : ℝ) :
    iteratedDeriv k (fun u : ℝ => ∫ x, f x * Real.exp (q x + u * s x) ∂μ) t =
      ∫ x, (f x * s x ^ k) * Real.exp (q x + t * s x) ∂μ := by
  induction k generalizing t with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, funext ih]
    have hfk : Integrable (fun x => f x * s x ^ k) μ :=
      integrable_mul_continuous_of_compact_support hμ hf (hs.pow k)
    rw [(hasDerivAt_integral_exponential_tilt hμ hq hs hfk t).deriv]
    congr 1
    funext x
    rw [pow_succ]
    ring

theorem hasDerivAt_tiltRawMoment {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : IsCompact μ.support)
    {q s : Space n → ℝ} (hq : Continuous q) (hs : Continuous s)
    (k : ℕ) (t : ℝ) :
    HasDerivAt (fun u : ℝ => tiltAverage μ (fun x => q x + u * s x) (fun x => s x ^ k))
      (tiltAverage μ (fun x => q x + t * s x) (fun x => s x ^ (k + 1)) -
        tiltAverage μ (fun x => q x + t * s x) (fun x => s x ^ k) *
        tiltAverage μ (fun x => q x + t * s x) s) t := by
  simpa only [pow_succ] using hasDerivAt_tiltAverage hμ hq hs
    (f := fun x => s x ^ k)
    (integrable_of_continuous_compact_support_measure hμ (by fun_prop)) t

theorem hasDerivAt_tiltMixedMoment {n m : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : IsCompact μ.support)
    {q s : Space n → ℝ} (hq : Continuous q) (hs : Continuous s)
    (v : Fin m → Space n → ℝ) (hv : ∀ i, Continuous (v i)) (t : ℝ) :
    HasDerivAt (fun u : ℝ => tiltAverage μ (fun x => q x + u * s x)
      (fun x => ∏ i, v i x))
      (tiltAverage μ (fun x => q x + t * s x) (fun x => (∏ i, v i x) * s x) -
        tiltAverage μ (fun x => q x + t * s x) (fun x => ∏ i, v i x) *
        tiltAverage μ (fun x => q x + t * s x) s) t :=
  hasDerivAt_tiltAverage hμ hq hs
    (integrable_of_continuous_compact_support_measure hμ (by fun_prop)) t

theorem contDiff_integral_exponential_tilt_nat {n : ℕ}
    {μ : Measure (Space n)} (hμ : IsCompact μ.support)
    {q s f : Space n → ℝ} (hq : Continuous q) (hs : Continuous s)
    (hf : Integrable f μ) (k : ℕ) :
    ContDiff ℝ k (fun u : ℝ => ∫ x, f x * Real.exp (q x + u * s x) ∂μ) := by
  induction k generalizing f with
  | zero =>
    rw [Nat.cast_zero, contDiff_zero]
    exact Differentiable.continuous
      (fun t => (hasDerivAt_integral_exponential_tilt hμ hq hs hf t).differentiableAt)
  | succ k ih =>
    rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_deriv]
    refine ⟨fun t => (hasDerivAt_integral_exponential_tilt hμ hq hs hf t).differentiableAt,
      (by simp), ?_⟩
    have he : deriv (fun u : ℝ => ∫ x, f x * Real.exp (q x + u * s x) ∂μ) =
        (fun t => ∫ x, (f x * s x) * Real.exp (q x + t * s x) ∂μ) :=
      funext (fun t => (hasDerivAt_integral_exponential_tilt hμ hq hs hf t).deriv)
    rw [he]
    exact ih (integrable_mul_continuous_of_compact_support hμ hf hs)

theorem contDiff_integral_exponential_tilt {n : ℕ}
    {μ : Measure (Space n)} (hμ : IsCompact μ.support)
    {q s f : Space n → ℝ} (hq : Continuous q) (hs : Continuous s)
    (hf : Integrable f μ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => ∫ x, f x * Real.exp (q x + u * s x) ∂μ) :=
  contDiff_infty.mpr (contDiff_integral_exponential_tilt_nat hμ hq hs hf)

theorem contDiff_tiltAverage {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : IsCompact μ.support)
    {q s f : Space n → ℝ} (hq : Continuous q) (hs : Continuous s)
    (hf : Integrable f μ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => tiltAverage μ (fun x => q x + u * s x) f) := by
  simp_rw [tiltAverage_eq_ratio]
  have hZ : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => tiltPartition μ (fun x => q x + u * s x)) := by
    simpa only [one_mul, tiltPartition] using
      contDiff_integral_exponential_tilt hμ hq hs (integrable_const (1 : ℝ))
  exact (contDiff_integral_exponential_tilt hμ hq hs hf).div hZ
    (fun t => (tiltPartition_pos hμ (by fun_prop)).ne')

end KLS
end

#print axioms KLS.iteratedDeriv_integral_exponential_tilt
#print axioms KLS.hasDerivAt_tiltRawMoment
#print axioms KLS.hasDerivAt_tiltMixedMoment
#print axioms KLS.contDiff_tiltAverage

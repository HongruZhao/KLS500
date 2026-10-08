import KLS.TiltDerivatives
import KLS.ThirdCumulant

/-!
# Multivariate smoothness of actual tilt numerators

Fréchet differentiation under the integral is justified by compact-support
domination. A finite coordinate decomposition then proves smoothness of every
order for integrable observables, without differentiability of the observable.
-/

open MeasureTheory Set Filter Metric
open scoped Topology BigOperators

noncomputable section
namespace KLS

def tiltNumerator {n : ℕ} (μ : Measure (Space n)) (q f : Space n → ℝ)
    (z : Space n) : ℝ := ∫ x, f x * Real.exp (q x + inner ℝ z x) ∂μ

def tiltLogLaplace {n : ℕ} (μ : Measure (Space n)) (z : Space n) : ℝ :=
  Real.log (tiltPartition μ (fun x => inner ℝ z x))

theorem hasFDerivAt_tiltNumerator_integral {n : ℕ}
    {μ : Measure (Space n)} (hμ : IsCompact μ.support)
    {q f : Space n → ℝ} (hq : Continuous q) (hf : Integrable f μ) (z : Space n) :
    HasFDerivAt (tiltNumerator μ q f)
      (∫ x, (f x * Real.exp (q x + inner ℝ z x)) • innerSL ℝ x ∂μ) z := by
  let D : Space n × Space n → Space n →L[ℝ] ℝ :=
    fun p => Real.exp (q p.2 + inner ℝ p.1 p.2) • innerSL ℝ p.2
  have hD : Continuous D := by dsimp [D]; fun_prop
  obtain ⟨C, hC⟩ := ((isCompact_closedBall z 1).prod hμ).exists_bound_of_continuousOn
    hD.continuousOn
  have hfi (w : Space n) : Integrable (fun x => f x * Real.exp (q x + inner ℝ w x)) μ :=
    integrable_mul_continuous_of_compact_support hμ hf (by fun_prop)
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := fun w x => (f x * Real.exp (q x + inner ℝ w x)) • innerSL ℝ x)
    (s := ball z 1) (bound := fun x => ‖f x‖ * C)
    (ball_mem_nhds z zero_lt_one)
    (Eventually.of_forall (fun w => (hfi w).aestronglyMeasurable)) (hfi z)
  · exact (hf.aestronglyMeasurable.mul (by fun_prop)).smul (by fun_prop)
  · filter_upwards [μ.support_mem_ae] with x hx
    intro w hw
    rw [mul_smul, norm_smul]
    exact mul_le_mul_of_nonneg_left (hC (w, x) ⟨mem_closedBall.mpr hw.le, hx⟩) (norm_nonneg _)
  · exact hf.norm.mul_const C
  · exact Eventually.of_forall fun x w _ => by
      simpa only [innerSL_apply_apply, real_inner_comm x, mul_smul] using
        ((((innerSL ℝ x).hasFDerivAt).const_add (q x)).exp).const_mul (f x)

theorem integrable_tiltNumerator_derivative {n : ℕ}
    {μ : Measure (Space n)} (hμ : IsCompact μ.support)
    {q f : Space n → ℝ} (hq : Continuous q) (hf : Integrable f μ) (z : Space n) :
    Integrable (fun x => (f x * Real.exp (q x + inner ℝ z x)) • innerSL ℝ x) μ := by
  have hc : Continuous (fun x => Real.exp (q x + inner ℝ z x) • innerSL ℝ x) := by fun_prop
  obtain ⟨C, hC⟩ := hμ.exists_bound_of_continuousOn hc.continuousOn
  have hi := hf.smul_bdd C hc.aestronglyMeasurable
    (show ∀ᵐ x ∂μ, ‖Real.exp (q x + inner ℝ z x) • innerSL ℝ x‖ ≤ C from by
      filter_upwards [μ.support_mem_ae] with x hx using hC x hx)
  simpa only [Pi.smul_def', mul_smul] using hi

theorem hasFDerivAt_tiltNumerator {n : ℕ}
    {μ : Measure (Space n)} (hμ : IsCompact μ.support)
    {q f : Space n → ℝ} (hq : Continuous q) (hf : Integrable f μ) (z : Space n) :
    HasFDerivAt (tiltNumerator μ q f)
      (∑ i, tiltNumerator μ q (fun x => f x * x i) z •
        (EuclideanSpace.proj i : Space n →L[ℝ] ℝ)) z := by
  convert hasFDerivAt_tiltNumerator_integral hμ hq hf z using 1
  ext y
  rw [ContinuousLinearMap.integral_apply (integrable_tiltNumerator_derivative hμ hq hf z)]
  simp only [sum_apply, smul_apply,
    EuclideanSpace.coe_proj, smul_eq_mul, innerSL_apply_apply, tiltNumerator]
  simp_rw [inner_eq_coordinate_sum (u := y), Finset.mul_sum]
  rw [integral_finsetSum Finset.univ (fun i _ =>
    integrable_mul_continuous_of_compact_support hμ hf (g := fun x =>
      Real.exp (q x + inner ℝ z x) * (y i * x i)) (by fun_prop) |>.congr
        (Eventually.of_forall (fun x => by ring)))]
  apply Finset.sum_congr rfl
  intro i _
  rw [← integral_mul_const]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by ring

theorem contDiff_tiltNumerator_nat {n : ℕ}
    {μ : Measure (Space n)} (hμ : IsCompact μ.support)
    {q f : Space n → ℝ} (hq : Continuous q) (hf : Integrable f μ) (k : ℕ) :
    ContDiff ℝ k (tiltNumerator μ q f) := by
  induction k generalizing f with
  | zero =>
    rw [Nat.cast_zero, contDiff_zero]
    exact Differentiable.continuous (fun z => (hasFDerivAt_tiltNumerator hμ hq hf z).differentiableAt)
  | succ k ih =>
    rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_fderiv]
    refine ⟨fun z => (hasFDerivAt_tiltNumerator hμ hq hf z).differentiableAt, by simp, ?_⟩
    have he : fderiv ℝ (tiltNumerator μ q f) =
        (fun z => ∑ i, tiltNumerator μ q (fun x => f x * x i) z •
          (EuclideanSpace.proj i : Space n →L[ℝ] ℝ)) :=
      funext (fun z => (hasFDerivAt_tiltNumerator hμ hq hf z).fderiv)
    rw [he]
    apply ContDiff.sum
    intro i _
    exact (ih (integrable_mul_continuous_of_compact_support hμ hf (by fun_prop))).smul contDiff_const

theorem contDiff_tiltNumerator {n : ℕ}
    {μ : Measure (Space n)} (hμ : IsCompact μ.support)
    {q f : Space n → ℝ} (hq : Continuous q) (hf : Integrable f μ) :
    ContDiff ℝ (⊤ : ℕ∞) (tiltNumerator μ q f) :=
  contDiff_infty.mpr (contDiff_tiltNumerator_nat hμ hq hf)

theorem contDiff_exponentialTilt_average {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : IsCompact μ.support)
    {f : Space n → ℝ} (hf : Integrable f μ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => ∫ x, f x ∂exponentialTilt μ z) := by
  change ContDiff ℝ (⊤ : ℕ∞) (fun z => tiltAverage μ (fun x => inner ℝ z x) f)
  simp_rw [tiltAverage_eq_ratio]
  have hN : ContDiff ℝ (⊤ : ℕ∞) (fun z => ∫ x, f x * Real.exp (inner ℝ z x) ∂μ) := by
    convert contDiff_tiltNumerator hμ (q := fun _ => 0) continuous_const hf using 1
    funext z
    simp only [tiltNumerator, zero_add]
  have hZ : ContDiff ℝ (⊤ : ℕ∞) (fun z => tiltPartition μ (fun x => inner ℝ z x)) := by
    convert contDiff_tiltNumerator hμ (q := fun _ => 0) continuous_const
      (integrable_const (1 : ℝ)) using 1
    funext z
    simp only [tiltNumerator, tiltPartition, zero_add, one_mul]
  exact hN.div hZ (fun z => (tiltPartition_pos hμ (by fun_prop)).ne')

theorem contDiff_tiltLogLaplace {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : IsCompact μ.support) :
    ContDiff ℝ (⊤ : ℕ∞) (tiltLogLaplace μ) := by
  have hZ : ContDiff ℝ (⊤ : ℕ∞) (fun z => tiltPartition μ (fun x => inner ℝ z x)) := by
    convert contDiff_tiltNumerator hμ (q := fun _ => 0) continuous_const
      (integrable_const (1 : ℝ)) using 1
    funext z
    simp only [tiltNumerator, tiltPartition, zero_add, one_mul]
  exact hZ.log (fun z => (tiltPartition_pos hμ (by fun_prop)).ne')

end KLS
end

#print axioms KLS.hasFDerivAt_tiltNumerator
#print axioms KLS.contDiff_tiltNumerator
#print axioms KLS.contDiff_exponentialTilt_average
#print axioms KLS.contDiff_tiltLogLaplace

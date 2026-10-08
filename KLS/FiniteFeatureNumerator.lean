import KLS.TiltFrechet

/-! Fréchet smoothness of compact-support exponential moments with any
continuous finite-dimensional feature map. -/
open MeasureTheory Set Filter Metric
open scoped Topology BigOperators
noncomputable section
namespace KLS.FiniteFeatureTilt

def featureNumerator {n m : ℕ} (μ : Measure (Space n)) (Φ : Space n → Space m)
    (q f : Space n → ℝ) (z : Space m) : ℝ :=
  ∫ x, f x * Real.exp (q x + inner ℝ z (Φ x)) ∂μ

theorem hasFDerivAt_featureNumerator_integral {n m : ℕ}
    {μ : Measure (Space n)} (hμ : IsCompact μ.support)
    {Φ : Space n → Space m} (hΦ : Continuous Φ)
    {q f : Space n → ℝ} (hq : Continuous q) (hf : Integrable f μ) (z : Space m) :
    HasFDerivAt (featureNumerator μ Φ q f)
      (∫ x, (f x * Real.exp (q x + inner ℝ z (Φ x))) • innerSL ℝ (Φ x) ∂μ) z := by
  let D : Space m × Space n → Space m →L[ℝ] ℝ :=
    fun p => Real.exp (q p.2 + inner ℝ p.1 (Φ p.2)) • innerSL ℝ (Φ p.2)
  have hD : Continuous D := by dsimp [D]; fun_prop
  obtain ⟨C, hC⟩ := ((isCompact_closedBall z 1).prod hμ).exists_bound_of_continuousOn
    hD.continuousOn
  have hfi (w : Space m) : Integrable (fun x => f x * Real.exp (q x + inner ℝ w (Φ x))) μ :=
    integrable_mul_continuous_of_compact_support hμ hf (by fun_prop)
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := fun w x => (f x * Real.exp (q x + inner ℝ w (Φ x))) • innerSL ℝ (Φ x))
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
      simpa only [innerSL_apply_apply, real_inner_comm (Φ x), mul_smul] using
        ((((innerSL ℝ (Φ x)).hasFDerivAt).const_add (q x)).exp).const_mul (f x)

theorem integrable_featureNumerator_derivative {n m : ℕ}
    {μ : Measure (Space n)} (hμ : IsCompact μ.support)
    {Φ : Space n → Space m} (hΦ : Continuous Φ)
    {q f : Space n → ℝ} (hq : Continuous q) (hf : Integrable f μ) (z : Space m) :
    Integrable (fun x => (f x * Real.exp (q x + inner ℝ z (Φ x))) • innerSL ℝ (Φ x)) μ := by
  have hc : Continuous (fun x => Real.exp (q x + inner ℝ z (Φ x)) • innerSL ℝ (Φ x)) := by fun_prop
  obtain ⟨C, hC⟩ := hμ.exists_bound_of_continuousOn hc.continuousOn
  have hi := hf.smul_bdd C hc.aestronglyMeasurable
    (show ∀ᵐ x ∂μ, ‖Real.exp (q x + inner ℝ z (Φ x)) • innerSL ℝ (Φ x)‖ ≤ C from by
      filter_upwards [μ.support_mem_ae] with x hx using hC x hx)
  simpa only [Pi.smul_def', mul_smul] using hi

theorem hasFDerivAt_featureNumerator {n m : ℕ}
    {μ : Measure (Space n)} (hμ : IsCompact μ.support)
    {Φ : Space n → Space m} (hΦ : Continuous Φ)
    {q f : Space n → ℝ} (hq : Continuous q) (hf : Integrable f μ) (z : Space m) :
    HasFDerivAt (featureNumerator μ Φ q f)
      (∑ i, featureNumerator μ Φ q (fun x => f x * Φ x i) z •
        (EuclideanSpace.proj i : Space m →L[ℝ] ℝ)) z := by
  convert hasFDerivAt_featureNumerator_integral hμ hΦ hq hf z using 1
  ext y
  rw [ContinuousLinearMap.integral_apply (integrable_featureNumerator_derivative hμ hΦ hq hf z)]
  simp only [sum_apply, smul_apply,
    EuclideanSpace.coe_proj, smul_eq_mul, innerSL_apply_apply, featureNumerator]
  simp_rw [inner_eq_coordinate_sum (u := y), Finset.mul_sum]
  rw [integral_finsetSum Finset.univ (fun i _ =>
    integrable_mul_continuous_of_compact_support hμ hf (g := fun x =>
      Real.exp (q x + inner ℝ z (Φ x)) * (y i * Φ x i)) (by fun_prop) |>.congr
        (Eventually.of_forall (fun x => by ring)))]
  apply Finset.sum_congr rfl
  intro i _
  rw [← integral_mul_const]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by ring

theorem contDiff_featureNumerator_nat {n m : ℕ}
    {μ : Measure (Space n)} (hμ : IsCompact μ.support)
    {Φ : Space n → Space m} (hΦ : Continuous Φ)
    {q f : Space n → ℝ} (hq : Continuous q) (hf : Integrable f μ) (k : ℕ) :
    ContDiff ℝ k (featureNumerator μ Φ q f) := by
  induction k generalizing f with
  | zero =>
    rw [Nat.cast_zero, contDiff_zero]
    exact Differentiable.continuous (fun z => (hasFDerivAt_featureNumerator hμ hΦ hq hf z).differentiableAt)
  | succ k ih =>
    rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_fderiv]
    refine ⟨fun z => (hasFDerivAt_featureNumerator hμ hΦ hq hf z).differentiableAt, by simp, ?_⟩
    have he : fderiv ℝ (featureNumerator μ Φ q f) =
        (fun z => ∑ i, featureNumerator μ Φ q (fun x => f x * Φ x i) z •
          (EuclideanSpace.proj i : Space m →L[ℝ] ℝ)) :=
      funext (fun z => (hasFDerivAt_featureNumerator hμ hΦ hq hf z).fderiv)
    rw [he]
    apply ContDiff.sum
    intro i _
    exact (ih (integrable_mul_continuous_of_compact_support hμ hf (by fun_prop))).smul contDiff_const

theorem contDiff_featureNumerator {n m : ℕ}
    {μ : Measure (Space n)} (hμ : IsCompact μ.support)
    {Φ : Space n → Space m} (hΦ : Continuous Φ)
    {q f : Space n → ℝ} (hq : Continuous q) (hf : Integrable f μ) :
    ContDiff ℝ (⊤ : ℕ∞) (featureNumerator μ Φ q f) :=
  contDiff_infty.mpr (contDiff_featureNumerator_nat hμ hΦ hq hf)


end KLS.FiniteFeatureTilt
end
#print axioms KLS.FiniteFeatureTilt.hasFDerivAt_featureNumerator
#print axioms KLS.FiniteFeatureTilt.contDiff_featureNumerator

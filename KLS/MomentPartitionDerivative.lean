import KLS.MomentPerturbationDerivative
import KLS.LocalRademacher

/-!
# Differentiation of the actual partition function

Rademacher gives the pointwise envelope derivative almost everywhere. A
uniform integrable bound on the difference quotient justifies moving this
derivative through Lebesgue integration.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

noncomputable section
namespace KLS

/-- A scalar version of mathlib's dominated derivative theorem with a bound
on increments from the base point. The derivative's integrability is explicit. -/
theorem hasDerivAt_integral_of_dominated_sub_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {F : ℝ → α → ℝ}
    {F' bound : α → ℝ} {s : Set ℝ} {t₀ : ℝ}
    (hs : s ∈ 𝓝 t₀) (hFmeas : ∀ t ∈ s, AEStronglyMeasurable (F t) μ)
    (hFint : Integrable (F t₀) μ) (hF'int : Integrable F' μ)
    (hbound : ∀ᵐ x ∂μ, ∀ t ∈ s, ‖F t x - F t₀ x‖ ≤ bound x * ‖t - t₀‖)
    (hboundint : Integrable bound μ)
    (hderiv : ∀ᵐ x ∂μ, HasDerivAt (fun t => F t x) (F' x) t₀) :
    HasDerivAt (fun t => ∫ x, F t x ∂μ) (∫ x, F' x ∂μ) t₀ := by
  let T : ℝ →L[ℝ] (ℝ →L[ℝ] ℝ) := ContinuousLinearMap.smulRightL ℝ ℝ ℝ 1
  have hm : AEStronglyMeasurable (T ∘ F') μ :=
    T.continuous.comp_aestronglyMeasurable hF'int.aestronglyMeasurable
  have hd : ∀ᵐ x ∂μ, HasFDerivAt (fun t => F t x) (T (F' x)) t₀ :=
    hderiv.mono fun x hx => hx.hasFDerivAt
  have hk := (hasFDerivAt_integral_of_dominated_loc_of_lip'
    hs hFmeas hFint hm hbound hboundint hd).2
  rw [hasDerivAt_iff_hasFDerivAt]
  simpa only [Function.comp_def, ContinuousLinearMap.integral_comp_comm _ hF'int] using! hk

theorem exp_neg_momentLegendrePerturbation_sub_bound
    {n : ℕ} {φ : Space n → ℝ} (hcont : Continuous φ)
    (hconvex : ConvexOn ℝ Set.univ φ) (hzero : φ 0 = 0) (hnonneg : ∀ x, 0 ≤ φ x)
    {v : Space n → ℝ} {B : ℝ} (hv : ∀ y, |v y| ≤ B) {t : ℝ}
    (ht : |t| < (B + 1)⁻¹) (x : Space n) :
    |Real.exp (-momentLegendrePerturbation φ v t x) - Real.exp (-φ x)| ≤
      (2 * B * Real.exp (-φ x)) * |t| := by
  have hB : 0 ≤ B := (abs_nonneg (v 0)).trans (hv 0)
  have htB : |t| * B ≤ 1 := by
    have h := (lt_div_iff₀ (show 0 < B + 1 by linarith)).mp (show |t| < 1 / (B + 1) by simpa only [one_div] using ht)
    nlinarith [abs_nonneg t]
  have hδ := abs_momentLegendrePerturbation_sub_le hcont hconvex hzero hnonneg hv t x
  have hs : |-(momentLegendrePerturbation φ v t x - φ x)| ≤ 1 := by
    simpa only [abs_neg] using hδ.trans htB
  have hexp := Real.abs_exp_sub_one_le hs
  have heq : Real.exp (-momentLegendrePerturbation φ v t x) - Real.exp (-φ x) =
      Real.exp (-φ x) * (Real.exp (-(momentLegendrePerturbation φ v t x - φ x)) - 1) := by
    rw [mul_sub, ← Real.exp_add, mul_one]
    congr 2
    ring
  rw [heq, abs_mul, Real.abs_exp]
  calc
    _ ≤ Real.exp (-φ x) * (2 * |-(momentLegendrePerturbation φ v t x - φ x)|) :=
      mul_le_mul_of_nonneg_left hexp (Real.exp_pos _).le
    _ ≤ Real.exp (-φ x) * (2 * (|t| * B)) := by
      gcongr
      simpa only [abs_neg] using hδ
    _ = (2 * B * Real.exp (-φ x)) * |t| := by ring

/-- Actual differentiation under the partition integral. -/
theorem hasDerivAt_momentPartitionFunction {n : ℕ} {φ : Space n → ℝ} {L : ℝ≥0}
    (hLip : LipschitzWith L φ) (hconvex : ConvexOn ℝ Set.univ φ)
    (hzero : φ 0 = 0) (hnonneg : ∀ x, 0 ≤ φ x)
    (hZ : Integrable (fun x => Real.exp (-φ x)) volume)
    {v : Space n → ℝ} {B : ℝ} (hv : ∀ y, |v y| ≤ B) (hvc : Continuous v) :
    HasDerivAt (fun t => momentPartitionFunction (momentLegendrePerturbation φ v t))
      (∫ x, Real.exp (-φ x) * v (gradient φ x)) 0 := by
  have hB : 0 ≤ B := (abs_nonneg (v 0)).trans (hv 0)
  have hz : momentLegendrePerturbation φ v 0 = φ := by
    funext x
    exact momentLegendrePerturbation_zero hLip.continuous hconvex hzero hnonneg v x
  have hvmeas : AEStronglyMeasurable (fun x => v (gradient φ x)) volume :=
    (hvc.measurable.comp (measurable_gradient φ)).aestronglyMeasurable
  have hderivInt : Integrable (fun x => Real.exp (-φ x) * v (gradient φ x)) volume :=
    hZ.mul_bdd hvmeas (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hv (gradient φ x))
  change HasDerivAt (fun t => ∫ x, Real.exp (-momentLegendrePerturbation φ v t x)) _ 0
  apply hasDerivAt_integral_of_dominated_sub_le
    (s := Metric.ball 0 (B + 1)⁻¹) (bound := fun x => 2 * B * Real.exp (-φ x))
  · exact Metric.ball_mem_nhds _ (inv_pos.mpr (by linarith))
  · intro t _
    exact ((lipschitzWith_momentLegendrePerturbation hLip hzero hnonneg hv t).continuous.neg.rexp).aestronglyMeasurable
  · simpa only [hz] using hZ
  · exact hderivInt
  · apply Eventually.of_forall
    intro x t ht
    rw [hz]
    simpa [Real.norm_eq_abs, sub_zero] using exp_neg_momentLegendrePerturbation_sub_bound
      hLip.continuous hconvex hzero hnonneg hv (by simpa [Metric.mem_ball, Real.dist_eq] using ht) x
  · exact hZ.const_mul _
  · filter_upwards [hLip.ae_differentiableAt (μ := (volume : Measure (Space n)))] with x hx
    have hd := hasDerivAt_momentLegendrePerturbation hLip.continuous hconvex hzero hnonneg
      hv hx.hasGradientAt hvc.continuousAt
    simpa only [Pi.neg_apply, neg_neg, hz] using hd.neg.exp

/-- Differentiating the proved two-sided variational inequality gives the
Euler--Lagrange identity against an arbitrary bounded continuous test. -/
theorem momentVariational_integral_identity {n : ℕ} {μ : Measure (Space n)}
    {φ : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L φ)
    (hconvex : ConvexOn ℝ Set.univ φ) (hzero : φ 0 = 0) (hnonneg : ∀ x, 0 ≤ φ x)
    (hZ : Integrable (fun x => Real.exp (-φ x)) volume)
    {v : Space n → ℝ} {B : ℝ} (hv : ∀ y, |v y| ≤ B) (hvc : Continuous v)
    (hvar : ∀ t : ℝ,
      Real.log (momentPartitionFunction (momentLegendrePerturbation φ v t)) -
        Real.log (momentPartitionFunction φ) ≤ t * (∫ y, v y ∂μ)) :
    (∫ x, Real.exp (-φ x) * v (gradient φ x)) / momentPartitionFunction φ =
      ∫ y, v y ∂μ := by
  have hz : momentLegendrePerturbation φ v 0 = φ := by
    funext x
    exact momentLegendrePerturbation_zero hLip.continuous hconvex hzero hnonneg v x
  have hpos : 0 < momentPartitionFunction φ := integral_exp_pos hZ
  have hd := (hasDerivAt_momentPartitionFunction hLip hconvex hzero hnonneg hZ hv hvc).log
    (by simpa only [hz] using hpos.ne')
  have hm : IsLocalMax (fun t =>
      Real.log (momentPartitionFunction (momentLegendrePerturbation φ v t)) -
        t * (∫ y, v y ∂μ)) 0 := by
    apply Eventually.of_forall
    intro t
    simp only [hz, zero_mul, sub_zero]
    linarith [hvar t]
  have hh := hm.hasDerivAt_eq_zero (hd.sub ((hasDerivAt_id (0 : ℝ)).mul_const (∫ y, v y ∂μ)))
  simp only [hz, one_mul] at hh
  linarith

/-- Actual bounded-target construction through the first-variation equation. -/
theorem IsIsotropic.exists_moment_potential_integral_identity
    {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : IsIsotropic μ)
    (L : ℝ≥0) (hbound : ∀ᵐ y ∂μ, ‖y‖ ≤ L) :
    ∃ φ : C(Space n, ℝ),
      φ ∈ normalizedConvexLipschitzPotentials n L ∧ (∀ x, 0 ≤ φ x) ∧
      momentDualEnergy μ φ ≠ ∞ ∧ Integrable (fun x => Real.exp (-φ x)) volume ∧
      ∀ (v : Space n → ℝ) (B : ℝ), (∀ y, |v y| ≤ B) → Continuous v →
        (∫ x, Real.exp (-φ x) * v (gradient φ x)) / momentPartitionFunction φ = ∫ y, v y ∂μ := by
  obtain ⟨φ, hφ, hnonneg, hfinite, hvar⟩ :=
    hμ.exists_momentVariational_potential_with_inequality L hbound
  obtain ⟨a, ha, hcone⟩ := hμ.exists_dualEnergy_linear_coercivity
  have hZ := integrable_exp_neg_of_linear_coercivity φ.continuous.aestronglyMeasurable
    ha (hcone φ hnonneg hfinite)
  refine ⟨φ, hφ, hnonneg, hfinite, hZ, ?_⟩
  intro v B hv hvc
  have hvi : Integrable v μ := Integrable.of_bound hvc.aestronglyMeasurable B
    (Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hv y)
  exact momentVariational_integral_identity hφ.1 hφ.2.2 hφ.2.1 hnonneg hZ hv hvc
    (hvar v B hv hvi)

end KLS
end

#print axioms KLS.hasDerivAt_integral_of_dominated_sub_le
#print axioms KLS.hasDerivAt_momentPartitionFunction

#print axioms KLS.momentVariational_integral_identity
#print axioms KLS.IsIsotropic.exists_moment_potential_integral_identity

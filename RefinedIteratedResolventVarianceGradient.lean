import RefinedIteratedResolventNumerics
import KLS.VarianceGradientLawApproximation

open MeasureTheory ProbabilityTheory InnerProductSpace Set Filter
open scoped Topology ContDiff ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace KLS
open ConstantReduction
variable {n : ℕ} {φ : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure φ)]

theorem variance_le_gradient_L1_of_poincare_smooth_bounded_refinedIterated
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hconv : ConvexOn ℝ univ φ)
    {C : ℝ≥0} (hC : C ∈ poincareConstants (potentialMeasure φ)) (hC0 : 0 < (C : ℝ))
    {f : Space n → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf2 : MemLp f 2 (potentialMeasure φ))
    {B M : ℝ} (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hfB : ∀ x, |f x| ≤ B) (hfM : ∀ x, ‖gradient f x‖ ≤ M) :
    ProbabilityTheory.variance f (potentialMeasure φ) ≤
      (223/100 : ℝ)*B*Real.sqrt C*(∫ x, ‖gradient f x‖ ∂potentialMeasure φ) := by
  have hfaithful : LocallyLipschitzTests (potentialMeasure φ) f :=
    ⟨(hf.of_le (by simp) : ContDiff ℝ 1 f).locallyLipschitz,hf2⟩
  have he : energy (potentialMeasure φ) f < ⊤ := by
    apply energy_lt_top_of_memLp_coordinateDerivative
    intro i
    apply MemLp.of_bound (measurable_coordinateDerivative f i).aestronglyMeasurable M
    exact Eventually.of_forall fun x => (norm_coordinateDerivative_le f i x).trans (hfM x)
  have ht : 0 < (C : ℝ)/51842 := by positivity
  have hu := weightedMassResolvent_finite_iterate_dual_bound hφ hconv ht
    hf hf2 hB hM hfB hfM hfaithful he 65534
  have hl := weightedMassResolvent_iterate_defect_pairing_ge hφ.continuous hC ht 65536 (hf2.toLp f)
  have hc : (C : ℝ)/((C : ℝ)+(C : ℝ)/51842)=51842/51843 := by field_simp; ring
  rw [hc,CenteredL2.norm_center_sq_eq_variance,ProbabilityTheory.variance_congr hf2.coeFn_toLp] at hl
  have hcoef := finite_resolvent_displacement_coefficient_le ht hB 65534
  have hnum := mul_le_mul_of_nonneg_right (refined_iterated_resolvent_displacement_certificate hC0) hB
  have hcoef' :
      2*Real.sqrt 2*B*Real.sqrt ((C:ℝ)/51842) +
        (∑ j ∈ Finset.range 65534, ((C:ℝ)/51842)*(B/Real.sqrt (2*((j:ℝ)+2)*((C:ℝ)/51842)))) ≤
      (257/161)*B*Real.sqrt C := by
    exact hcoef.trans (by simpa only [Nat.cast_ofNat, mul_assoc, mul_left_comm, mul_comm] using hnum)
  have hI : 0 ≤ ∫ x, ‖gradient f x‖ ∂potentialMeasure φ := integral_nonneg fun x => norm_nonneg _
  have hu' : |inner ℝ
      (hf2.toLp f-(weightedMassResolvent φ ht)^[65536] (hf2.toLp f)) (hf2.toLp f)| ≤
      (257/161)*B*Real.sqrt C*(∫ x, ‖gradient f x‖ ∂potentialMeasure φ) := by
    exact hu.trans (mul_le_mul_of_nonneg_right hcoef' hI)
  have hp := le_abs_self (inner ℝ
    (hf2.toLp f-(weightedMassResolvent φ ht)^[65536] (hf2.toLp f)) (hf2.toLp f))
  have hgap := mul_le_mul_of_nonneg_right
    (show (717/1000 : ℝ) ≤ 1-(51842/51843 : ℝ)^65536 by
      calc
        _ = 1-(283/1000 : ℝ) := by norm_num
        _ ≤ _ := sub_le_sub_left refined_iterated_resolvent_contraction_certificate 1)
    (ProbabilityTheory.variance_nonneg f (potentialMeasure φ))
  have hlow := hgap.trans hl
  have hpositive : 0 ≤ B*Real.sqrt (C:ℝ)*(∫ x, ‖gradient f x‖ ∂potentialMeasure φ) := by positivity
  nlinarith

theorem variance_le_gradient_L1_of_poincare_smooth_compact_refinedIterated
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hconv : ConvexOn ℝ univ φ)
    {C : ℝ≥0} (hC : C ∈ poincareConstants (potentialMeasure φ)) (hC0 : 0 < (C : ℝ))
    {f : Space n → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    {B : ℝ} (hB : 0 ≤ B) (hfB : ∀ x, |f x| ≤ B) :
    ProbabilityTheory.variance f (potentialMeasure φ) ≤
      (223/100 : ℝ)*B*Real.sqrt C*(∫ x, ‖gradient f x‖ ∂potentialMeasure φ) := by
  have hf2 := memLp_of_continuous_hasCompactSupport hφ.continuous hf.continuous hfc
  obtain ⟨M,hM⟩ := (hasCompactSupport_gradient hfc).exists_bound_of_continuous
    (continuous_gradient_of_contDiff (hf.of_le (by simp) : ContDiff ℝ 1 f))
  exact variance_le_gradient_L1_of_poincare_smooth_bounded_refinedIterated hφ hconv hC hC0 hf hf2 hB
    ((norm_nonneg (gradient f 0)).trans (hM 0)) hfB hM

theorem smoothVarianceBound_of_strongDensity_poincare_refinedIterated
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hdensity : HasSmoothStronglyConvexDensity μ)
    {C : ℝ≥0} (hC : C ∈ poincareConstants μ) (hC0 : 0 < (C : ℝ)) :
    SmoothCompactVarianceGradientBound μ ((223/100 : ℝ)*Real.sqrt C) := by
  obtain ⟨V,κ,hV,hκ,hstrong,heq⟩ := hdensity
  subst μ
  intro f hf hc B hB hfB
  have hb := variance_le_gradient_L1_of_poincare_smooth_compact_refinedIterated hV
    (convexOn_of_strongConvexOn_nonneg hκ.le hstrong) hC hC0 hf hc hB hfB
  convert hb using 1
  ring

theorem admissibleMeasure.boundedVarianceBound_of_uniform_strong_poincare_refinedIterated
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {C : ℝ≥0} (hC0 : 0 < (C : ℝ))
    (hstrong : ∀ ν : Measure (Space n), admissibleMeasure ν →
      HasSmoothStronglyConvexDensity ν → C ∈ poincareConstants ν) :
    BoundedVarianceGradientBound μ ((223/100 : ℝ)*Real.sqrt C) := by
  apply hμ.boundedVarianceBound_of_global_strongDensity
  intro ν hν hdensity
  let : IsProbabilityMeasure ν := hν.isProb
  exact smoothVarianceBound_of_strongDensity_poincare_refinedIterated hdensity
    (hstrong ν hν hdensity) hC0

end KLS
end

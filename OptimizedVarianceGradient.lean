import OptimizedResolventDisplacement
import KLS.VarianceGradientLawApproximation

open MeasureTheory ProbabilityTheory InnerProductSpace Set Filter
open scoped Topology ContDiff ENNReal NNReal RealInnerProductSpace

noncomputable section
namespace KLS
variable {n : ℕ} {φ : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure φ)]

/-- The exact partition limit and time C/2 give coefficient 18/5 instead of
16/3, for the same actual smooth bounded tests and literal L1 gradient. -/
theorem variance_le_gradient_L1_of_poincare_smooth_bounded_optimized
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hconv : ConvexOn ℝ univ φ)
    {C : ℝ≥0} (hC : C ∈ poincareConstants (potentialMeasure φ)) (hC0 : 0 < (C : ℝ))
    {f : Space n → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf2 : MemLp f 2 (potentialMeasure φ))
    {B M : ℝ} (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hfB : ∀ x, |f x| ≤ B) (hfM : ∀ x, ‖gradient f x‖ ≤ M) :
    ProbabilityTheory.variance f (potentialMeasure φ) ≤
      (18/5 : ℝ)*B*Real.sqrt C*(∫ x, ‖gradient f x‖ ∂potentialMeasure φ) := by
  have hfaithful : LocallyLipschitzTests (potentialMeasure φ) f :=
    ⟨(hf.of_le (by simp) : ContDiff ℝ 1 f).locallyLipschitz,hf2⟩
  have he : energy (potentialMeasure φ) f < ⊤ := by
    apply energy_lt_top_of_memLp_coordinateDerivative
    intro i
    apply MemLp.of_bound (measurable_coordinateDerivative f i).aestronglyMeasurable M
    exact Eventually.of_forall fun x => (norm_coordinateDerivative_le f i x).trans (hfM x)
  have ht : 0 < (C : ℝ)/2 := by positivity
  have hu := weightedMassResolvent_square_dual_displacement_le_optimized hφ hconv ht
    hf hf2 hB hM hfB hfM hfaithful he
  have hl := weightedMassResolvent_square_defect_pairing_ge hφ.continuous hC ht (hf2.toLp f)
  have hc : (C : ℝ)/((C : ℝ)+(C : ℝ)/2)=2/3 := by field_simp; ring
  rw [hc,CenteredL2.norm_center_sq_eq_variance,ProbabilityTheory.variance_congr hf2.coeFn_toLp] at hl
  have hs : Real.sqrt 2*Real.sqrt ((C : ℝ)/2)=Real.sqrt C := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have hu' : |inner ℝ
      (hf2.toLp f-weightedMassResolvent φ ht (weightedMassResolvent φ ht (hf2.toLp f))) (hf2.toLp f)| ≤
      2*B*Real.sqrt C*(∫ x, ‖gradient f x‖ ∂potentialMeasure φ) := by
    calc
      _ ≤ _ := hu
      _ = 2*B*(Real.sqrt 2*Real.sqrt ((C : ℝ)/2))*
          (∫ x, ‖gradient f x‖ ∂potentialMeasure φ) := by ring
      _ = _ := by rw [hs]
  have hp := le_abs_self (inner ℝ
    (hf2.toLp f-weightedMassResolvent φ ht (weightedMassResolvent φ ht (hf2.toLp f))) (hf2.toLp f))
  nlinarith

/-- Compact support supplies all domains and bounds for the sharper estimate. -/
theorem variance_le_gradient_L1_of_poincare_smooth_compact_optimized
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hconv : ConvexOn ℝ univ φ)
    {C : ℝ≥0} (hC : C ∈ poincareConstants (potentialMeasure φ)) (hC0 : 0 < (C : ℝ))
    {f : Space n → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    {B : ℝ} (hB : 0 ≤ B) (hfB : ∀ x, |f x| ≤ B) :
    ProbabilityTheory.variance f (potentialMeasure φ) ≤
      (18/5 : ℝ)*B*Real.sqrt C*(∫ x, ‖gradient f x‖ ∂potentialMeasure φ) := by
  have hf2 := memLp_of_continuous_hasCompactSupport hφ.continuous hf.continuous hfc
  obtain ⟨M,hM⟩ := (hasCompactSupport_gradient hfc).exists_bound_of_continuous
    (continuous_gradient_of_contDiff (hf.of_le (by simp) : ContDiff ℝ 1 f))
  exact variance_le_gradient_L1_of_poincare_smooth_bounded_optimized hφ hconv hC hC0 hf hf2 hB
    ((norm_nonneg (gradient f 0)).trans (hM 0)) hfB hM

/-- The sharper coefficient extends through the same full-class approximation. -/
theorem smoothVarianceBound_of_strongDensity_poincare_optimized
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hdensity : HasSmoothStronglyConvexDensity μ)
    {C : ℝ≥0} (hC : C ∈ poincareConstants μ) (hC0 : 0 < (C : ℝ)) :
    SmoothCompactVarianceGradientBound μ ((18/5 : ℝ)*Real.sqrt C) := by
  obtain ⟨V,κ,hV,hκ,hstrong,heq⟩ := hdensity
  subst μ
  intro f hf hc B hB hfB
  have hb := variance_le_gradient_L1_of_poincare_smooth_compact_optimized hV
    (convexOn_of_strongConvexOn_nonneg hκ.le hstrong) hC hC0 hf hc hB hfB
  convert hb using 1
  ring

/-- Every original admissible law inherits the improved bounded-variance
estimate from one uniform faithful Poincare bound on its smooth approximants. -/
theorem admissibleMeasure.boundedVarianceBound_of_uniform_strong_poincare_optimized
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {C : ℝ≥0} (hC0 : 0 < (C : ℝ))
    (hstrong : ∀ ν : Measure (Space n), admissibleMeasure ν →
      HasSmoothStronglyConvexDensity ν → C ∈ poincareConstants ν) :
    BoundedVarianceGradientBound μ ((18/5 : ℝ)*Real.sqrt C) := by
  apply hμ.boundedVarianceBound_of_global_strongDensity
  intro ν hν hdensity
  let : IsProbabilityMeasure ν := hν.isProb
  exact smoothVarianceBound_of_strongDensity_poincare_optimized hdensity
    (hstrong ν hν hdensity) hC0

end KLS
end

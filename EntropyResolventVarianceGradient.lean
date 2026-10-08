import EntropyPolynomialDisplacement
import ProfileClockAssembly
import IteratedResolventSpectral
import KLS.VarianceGradientLawApproximation

open MeasureTheory ProbabilityTheory InnerProductSpace Set Filter
open scoped Topology ContDiff ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace KLS
open ConstantReduction
variable {n : ℕ} {φ : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure φ)]

/-- The explicit entropy profile gives conversion coefficient1.97 for actual
smooth tests with bounded value, gradient, and diffusion. -/
theorem variance_le_gradient_L1_of_poincare_entropy_bounded
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hconv : ConvexOn ℝ univ φ)
    {C : ℝ≥0} (hC : C ∈ poincareConstants (potentialMeasure φ)) (hC0 : 0 < (C : ℝ))
    {f : Space n → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf2 : MemLp f 2 (potentialMeasure φ))
    {B M L : ℝ} (hB : 0 < B) (hM : 0 ≤ M) (hL : 0 < L)
    (hfB : ∀ x, |f x| ≤ B) (hfM : ∀ x, ‖gradient f x‖ ≤ M)
    (hfL : ∀ x, |weightedDiffusion φ f x| ≤ L) :
    ProbabilityTheory.variance f (potentialMeasure φ) ≤
      (197/100 : ℝ)*B*Real.sqrt C*(∫ x, ‖gradient f x‖ ∂potentialMeasure φ) := by
  have hfaithful : LocallyLipschitzTests (potentialMeasure φ) f :=
    ⟨(hf.of_le (by simp) : ContDiff ℝ 1 f).locallyLipschitz,hf2⟩
  have he : energy (potentialMeasure φ) f < ⊤ := by
    apply energy_lt_top_of_memLp_coordinateDerivative
    intro i
    apply MemLp.of_bound (measurable_coordinateDerivative f i).aestronglyMeasurable M
    exact Eventually.of_forall fun x => (norm_coordinateDerivative_le f i x).trans (hfM x)
  obtain ⟨m,hm,ht,_hs,hN,_htime,hlag,_hprefix,_hcoef1,hcoef,hcontract⟩ :=
    profileClock_complete_finite_parameters hC0 hB hM hL
  have hu := weightedMassResolvent_finite_dual_polynomial_profile hφ hconv ht hB hM hlag
    hf hf2 hfB hfM hfL hfaithful he hN
  have hI : 0 ≤ ∫ x, ‖gradient f x‖ ∂potentialMeasure φ := integral_nonneg fun x => norm_nonneg _
  have hu' := hu.trans (mul_le_mul_of_nonneg_right hcoef hI)
  have hl := weightedMassResolvent_iterate_defect_pairing_ge hφ.continuous hC ht
    (128*m) (hf2.toLp f)
  rw [CenteredL2.norm_center_sq_eq_variance,ProbabilityTheory.variance_congr hf2.coeFn_toLp] at hl
  have hgap : (71/100 : ℝ)*ProbabilityTheory.variance f (potentialMeasure φ) ≤
      inner ℝ (hf2.toLp f-(weightedMassResolvent φ ht)^[128*m] (hf2.toLp f)) (hf2.toLp f) := by
    have hh := mul_le_mul_of_nonneg_right
      (show (71/100 : ℝ) ≤ 1-((C : ℝ)/((C : ℝ)+5*(C : ℝ)/(512*(m : ℝ))))^(128*m) by linarith)
      (ProbabilityTheory.variance_nonneg f (potentialMeasure φ))
    exact hh.trans hl
  have hp := le_abs_self (inner ℝ
    (hf2.toLp f-(weightedMassResolvent φ ht)^[128*m] (hf2.toLp f)) (hf2.toLp f))
  have hpositive : 0 ≤ B*Real.sqrt (C : ℝ)*(∫ x, ‖gradient f x‖ ∂potentialMeasure φ) := by positivity
  nlinarith only [hgap,hp,hu',hpositive]

/-- Compact smooth tests provide all gradient and diffusion bounds needed by
the actual finite entropy argument. The zero value-bound case is explicit. -/
theorem variance_le_gradient_L1_of_poincare_entropy_compact
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hconv : ConvexOn ℝ univ φ)
    {C : ℝ≥0} (hC : C ∈ poincareConstants (potentialMeasure φ)) (hC0 : 0 < (C : ℝ))
    {f : Space n → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    {B : ℝ} (hB : 0 ≤ B) (hfB : ∀ x, |f x| ≤ B) :
    ProbabilityTheory.variance f (potentialMeasure φ) ≤
      (197/100 : ℝ)*B*Real.sqrt C*(∫ x, ‖gradient f x‖ ∂potentialMeasure φ) := by
  rcases hB.eq_or_lt with hBzero | hBpos
  · have hz : f=fun _ => (0 : ℝ) := by
      funext x
      have hh := hfB x
      rw [←hBzero] at hh
      exact abs_eq_zero.mp (le_antisymm hh (abs_nonneg _))
    rw [hz]
    simp [ProbabilityTheory.variance,ProbabilityTheory.evariance]
  · have hf2 := memLp_of_continuous_hasCompactSupport hφ.continuous hf.continuous hfc
    obtain ⟨M,L,hM,hL,hfM,hfL⟩ := smoothCompact_exists_gradient_diffusion_bounds
      (hφ.of_le (by simp)) (hf.of_le (by simp)) hfc
    exact variance_le_gradient_L1_of_poincare_entropy_bounded hφ hconv hC hC0 hf hf2
      hBpos hM hL hfB hfM hfL

theorem smoothVarianceBound_of_strongDensity_poincare_entropy
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hdensity : HasSmoothStronglyConvexDensity μ)
    {C : ℝ≥0} (hC : C ∈ poincareConstants μ) (hC0 : 0 < (C : ℝ)) :
    SmoothCompactVarianceGradientBound μ ((197/100 : ℝ)*Real.sqrt C) := by
  obtain ⟨V,κ,hV,hκ,hstrong,heq⟩ := hdensity
  subst μ
  intro f hf hc B hB hfB
  have hb := variance_le_gradient_L1_of_poincare_entropy_compact hV
    (convexOn_of_strongConvexOn_nonneg hκ.le hstrong) hC hC0 hf hc hB hfB
  convert hb using 1
  ring

theorem admissibleMeasure.boundedVarianceBound_of_uniform_strong_poincare_entropy
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {C : ℝ≥0} (hC0 : 0 < (C : ℝ))
    (hstrong : ∀ ν : Measure (Space n), admissibleMeasure ν →
      HasSmoothStronglyConvexDensity ν → C ∈ poincareConstants ν) :
    BoundedVarianceGradientBound μ ((197/100 : ℝ)*Real.sqrt C) := by
  apply hμ.boundedVarianceBound_of_global_strongDensity
  intro ν hν hdensity
  let : IsProbabilityMeasure ν := hν.isProb
  exact smoothVarianceBound_of_strongDensity_poincare_entropy hdensity (hstrong ν hν hdensity) hC0

end KLS
end

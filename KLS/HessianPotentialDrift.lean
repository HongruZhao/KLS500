import KLS.HessianMetricL1DriftCutoff
import KLS.MomentMapIntegration
import KLS.LocalRademacher

/-!
# Integrable potential drift from actual target moments

The diffusion of the source potential equals n minus the target gradient
paired with the transported point. Linear growth of the target gradient and
isotropy of the actual gradient pushforward therefore give its L¹ bound.
-/

open MeasureTheory InnerProductSpace Matrix Set Filter
open scoped ContDiff BigOperators

noncomputable section
namespace KLS

variable {n : ℕ}

theorem hessianMetricDiffusion_potential_eq {φ : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    (V : Space n → ℝ) (x : Space n) :
    hessianMetricDiffusion φ V φ x =
      (n : ℝ) - inner ℝ (gradient V (gradient φ x)) (gradient φ x) := by
  rw [← hessianMetricDiffusion_potentialHeight_eq φ V (0 : Space n) x,
    hessianMetricDiffusion_potentialHeight hφ hpos]
  simp only [coordinateDerivative_eq_gradient, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, star_trivial, mul_comm]

theorem integrable_target_radial_gradient_of_linear_growth
    {μ : Measure (Space n)} (hiso : IsIsotropic μ) (V : Space n → ℝ)
    {a b : ℝ} (hgrowth : ∀ y, ‖gradient V y‖ ≤ a + b * ‖y‖) :
    Integrable (fun y => inner ℝ (gradient V y) y) μ := by
  have hmajor : Integrable (fun y : Space n => a * ‖y‖ + b * ‖y‖ ^ 2) μ :=
    (hiso.1.norm.const_mul a).add (hiso.integrable_norm_sq.const_mul b)
  apply hmajor.mono' ((measurable_gradient V).inner measurable_id).aestronglyMeasurable
  exact Eventually.of_forall fun y => calc
    ‖inner ℝ (gradient V y) y‖ ≤ ‖gradient V y‖ * ‖y‖ := norm_inner_le_norm _ _
    _ ≤ (a + b * ‖y‖) * ‖y‖ := mul_le_mul_of_nonneg_right (hgrowth y) (norm_nonneg _)
    _ = a * ‖y‖ + b * ‖y‖ ^ 2 := by ring

theorem integrable_hessianMetricDiffusion_potential_of_linear_growth
    {φ V : Space n → ℝ} [IsFiniteMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    (hiso : IsIsotropic (MomentMap.gradientPushforward φ))
    {a b : ℝ} (hgrowth : ∀ y, ‖gradient V y‖ ≤ a + b * ‖y‖) :
    Integrable (hessianMetricDiffusion φ V φ) (potentialMeasure φ) := by
  have hi := integrable_target_radial_gradient_of_linear_growth hiso V hgrowth
  have hc : Integrable (fun x => inner ℝ (gradient V (gradient φ x)) (gradient φ x))
      (potentialMeasure φ) := hi.comp_aemeasurable (measurable_gradient φ).aemeasurable
  have heq : hessianMetricDiffusion φ V φ =
      fun x => (n : ℝ) - inner ℝ (gradient V (gradient φ x)) (gradient φ x) :=
    funext (hessianMetricDiffusion_potential_eq hφ hpos V)
  rw [heq]
  exact (integrable_const (n : ℝ)).sub hc

end KLS
end

#print axioms KLS.hessianMetricDiffusion_potential_eq
#print axioms KLS.integrable_target_radial_gradient_of_linear_growth
#print axioms KLS.integrable_hessianMetricDiffusion_potential_of_linear_growth

import KLS.GaussianAdditiveStein
import KLS.AffineMomentMapContraction
import KLS.WeightedSmoothVariance

/-!
# Gaussian addition only in the moment-map Stein step

The source potential and its Hessian are unchanged. The actual target is
the law of `A gradient(phi)(Y) + r G`; its Stein action in the fixed product
coupling is `A Hessian(phi)(Y) Aᵀ w + r² w`. Smooth full-space variance duality
is applied to this target, with its density representation kept explicit.
-/

open MeasureTheory ProbabilityTheory InnerProductSpace Set Filter Matrix
open scoped ContDiff Topology BigOperators RealInnerProductSpace

noncomputable section
namespace KLS
namespace MomentMap

variable {n : ℕ}

lemma linearGradientPushforward_eq_map {φ : Space n → ℝ}
    (hgrad : Continuous (gradient φ)) (A : Matrix (Fin n) (Fin n) ℝ) :
    linearGradientPushforward φ A =
      (potentialMeasure φ).map (fun x => matrixAction A (gradient φ x)) := by
  rw [linearGradientPushforward, gradientPushforward,
    Measure.map_map (matrixAction A).continuous.measurable hgrad.measurable]
  rfl

lemma integral_gaussianSmoothing_linearGradientPushforward {φ f : Space n → ℝ}
    (hgrad : Continuous (gradient φ)) (A : Matrix (Fin n) (Fin n) ℝ)
    (hf : Measurable f) (r : ℝ) :
    (∫ z, f z ∂gaussianSmoothing (linearGradientPushforward φ A) r) =
      ∫ p, f (matrixAction A (gradient φ p.1) + r • p.2)
        ∂(potentialMeasure φ).prod (gaussianExample n) := by
  rw [linearGradientPushforward_eq_map hgrad,
    gaussianSmoothing_map_eq_map_prod _
      (show Measurable (fun x => matrixAction A (gradient φ x)) from
        (matrixAction A).continuous.measurable.comp hgrad.measurable),
    integral_map (by fun_prop) hf.aestronglyMeasurable]

theorem integral_smoothed_linear_target_sq_le_stein_energy {φ f : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hiso : IsIsotropic (gradientPushforward φ))
    {L : ℝ} (hL : ∀ x, ‖fderiv ℝ (gradient φ) x‖ ≤ L)
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (A : Matrix (Fin n) (Fin n) ℝ) (w : Space n) (r : ℝ) :
    (∫ z, f z * inner ℝ z w ∂gaussianSmoothing (linearGradientPushforward φ A) r) ^ 2 ≤
      (∫ x, ‖transportedGradientDerivative φ A x w + r ^ 2 • w‖ ^ 2 ∂potentialMeasure φ) *
        ∫ z, ‖gradient f z‖ ^ 2 ∂gaussianSmoothing (linearGradientPushforward φ A) r := by
  have hgrad := contDiff_gradient_of_contDiff_two hφ
  have hXm : Measurable (fun x => matrixAction A (gradient φ x)) :=
    (matrixAction A).continuous.measurable.comp hgrad.continuous.measurable
  have hg2 : MemLp (gradient φ) 2 (potentialMeasure φ) := by
    have hmap := hiso.memLp_id
    change MemLp (fun x : Space n => x) 2 ((potentialMeasure φ).map (gradient φ)) at hmap
    exact (memLp_map_measure_iff aestronglyMeasurable_id
      hgrad.continuous.measurable.aemeasurable).mp hmap
  have hX2 := (matrixAction A).comp_memLp' hg2
  have hT2 := memLp_transportedGradientDerivative hgrad hL A w
  have hs : ∀ h : Space n → ℝ, ContDiff ℝ 1 h → HasCompactSupport h →
      (∫ x, h (matrixAction A (gradient φ x)) * inner ℝ (matrixAction A (gradient φ x)) w
        ∂potentialMeasure φ) =
      ∫ x, inner ℝ (gradient h (matrixAction A (gradient φ x)))
        (transportedGradientDerivative φ A x w) ∂potentialMeasure φ := by
    intro h hh hc
    have he := integral_linear_target_mul_test_eq (hφ.differentiable (by norm_num))
      hgrad hh hc hL A w
    rw [integral_linearGradientPushforward (g := fun z => h z * inner ℝ z w) hgrad.continuous
      (hh.continuous.mul (continuous_id.inner continuous_const)).measurable A] at he
    exact he
  rw [integral_gaussianSmoothing_linearGradientPushforward (f := fun z => f z * inner ℝ z w)
      hgrad.continuous A
      (hf.continuous.mul (continuous_id.inner continuous_const)).measurable,
    integral_gaussianSmoothing_linearGradientPushforward (f := fun z => ‖gradient f z‖ ^ 2)
      hgrad.continuous A
      ((measurable_gradient f).norm.pow_const 2)]
  exact integral_gaussian_additive_stein_sq_le hXm hX2 hT2 w hs hf hc r

end MomentMap

theorem quadratic_gradient_dual_of_smoothed_linear_momentMap {n : ℕ}
    {φ V : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hiso : IsIsotropic (MomentMap.gradientPushforward φ))
    (A : Matrix (Fin n) (Fin n) ℝ) (r : ℝ)
    (hpush : gaussianSmoothing (MomentMap.linearGradientPushforward φ A) r = potentialMeasure V)
    {L : ℝ} (hL : ∀ x, ‖fderiv ℝ (gradient φ) x‖ ≤ L)
    (U : Matrix (Fin n) (Fin n) ℝ) (hU : U.IsSymm) (i : Fin n) :
    CoordinateGradientDualBound V (matrixQuadratic U) i
      (4 * ∫ x, ‖MomentMap.transportedGradientDerivative φ A x (WithLp.toLp 2 (U i)) +
        r ^ 2 • WithLp.toLp 2 (U i)‖ ^ 2 ∂potentialMeasure φ) := by
  intro h hh hc
  have hb := MomentMap.integral_smoothed_linear_target_sq_le_stein_energy
    hφ hiso hL hh hc A (WithLp.toLp 2 (U i)) r
  rw [hpush] at hb
  have heq : (∫ x, coordinateDerivative (matrixQuadratic U) i x * h x ∂potentialMeasure V) =
      2 * (∫ x, h x * inner ℝ x (WithLp.toLp 2 (U i)) ∂potentialMeasure V) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only
      rw [coordinateDerivative_matrixQuadratic U hU]
      ring
  rw [heq]
  nlinarith

theorem quadratic_variance_le_smoothed_linear_momentMap_energy {n : ℕ}
    {φ V : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
    [IsProbabilityMeasure (potentialMeasure V)]
    (hφ : ContDiff ℝ 2 φ) (hiso : IsIsotropic (MomentMap.gradientPushforward φ))
    (hV : ContDiff ℝ 2 V) (hconv : ConvexOn ℝ univ V)
    (A : Matrix (Fin n) (Fin n) ℝ) (r : ℝ)
    (hpush : gaussianSmoothing (MomentMap.linearGradientPushforward φ A) r = potentialMeasure V)
    {L : ℝ} (hL : ∀ x, ‖fderiv ℝ (gradient φ) x‖ ≤ L)
    (U : Matrix (Fin n) (Fin n) ℝ) (hU : U.IsSymm)
    (hq : MemLp (matrixQuadratic U) 2 (potentialMeasure V)) :
    ProbabilityTheory.variance (matrixQuadratic U) (potentialMeasure V) ≤
      4 * ∑ i : Fin n, ∫ x,
        ‖MomentMap.transportedGradientDerivative φ A x (WithLp.toLp 2 (U i)) +
          r ^ 2 • WithLp.toLp 2 (U i)‖ ^ 2 ∂potentialMeasure φ := by
  rw [Finset.mul_sum]
  exact variance_le_sum_gradient_dual_smooth hV hconv
    ((contDiff_matrixQuadratic U).of_le (by simp)) hq
    (fun i => mul_nonneg (by norm_num) (integral_nonneg fun _ => sq_nonneg _))
    (quadratic_gradient_dual_of_smoothed_linear_momentMap hφ hiso A r hpush hL U hU)

end KLS
end

#print axioms KLS.MomentMap.integral_smoothed_linear_target_sq_le_stein_energy
#print axioms KLS.quadratic_gradient_dual_of_smoothed_linear_momentMap
#print axioms KLS.quadratic_variance_le_smoothed_linear_momentMap_energy

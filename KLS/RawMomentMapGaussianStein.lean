import KLS.RawMomentMapStein
import KLS.GaussianMomentMapStein

open MeasureTheory ProbabilityTheory InnerProductSpace Set Filter Matrix
open scoped ContDiff Topology BigOperators RealInnerProductSpace NNReal
noncomputable section
namespace KLS
namespace MomentMap
variable {n : ℕ}

theorem integral_smoothed_linear_target_sq_le_raw_stein_energy_C11 {φ f : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 1 φ) (hiso : IsIsotropic (gradientPushforward φ))
    {G : ℝ≥0} (hG : LipschitzWith G (gradient φ))
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (A : Matrix (Fin n) (Fin n) ℝ) (w : Space n) (r : ℝ) :
    (∫ z, f z * inner ℝ z w ∂gaussianSmoothing (linearGradientPushforward φ A) r) ^ 2 ≤
      (∫ x, ‖rawTransportedHessianDerivative φ A x w + r ^ 2 • w‖ ^ 2 ∂potentialMeasure φ) *
        ∫ z, ‖gradient f z‖ ^ 2 ∂gaussianSmoothing (linearGradientPushforward φ A) r := by
  have hgrad : Continuous (gradient φ) := hG.continuous
  have hXm : Measurable (fun x => matrixAction A (gradient φ x)) :=
    (matrixAction A).continuous.measurable.comp hgrad.measurable
  have hg2 : MemLp (gradient φ) 2 (potentialMeasure φ) := by
    have hmap := hiso.memLp_id
    change MemLp (fun x : Space n => x) 2 ((potentialMeasure φ).map (gradient φ)) at hmap
    exact (memLp_map_measure_iff aestronglyMeasurable_id
      hgrad.measurable.aemeasurable).mp hmap
  have hX2 := (matrixAction A).comp_memLp' hg2
  have hT2 := memLp_rawTransportedHessianDerivative (μ := potentialMeasure φ) hG A w 2
  have hs : ∀ h : Space n → ℝ, ContDiff ℝ 1 h → HasCompactSupport h →
      (∫ x, h (matrixAction A (gradient φ x)) * inner ℝ (matrixAction A (gradient φ x)) w
        ∂potentialMeasure φ) =
      ∫ x, inner ℝ (gradient h (matrixAction A (gradient φ x)))
        (rawTransportedHessianDerivative φ A x w) ∂potentialMeasure φ := by
    intro h hh hc
    have he := integral_linear_target_mul_test_eq_raw_C11 hφ hG hiso hh hc A w
    rw [integral_linearGradientPushforward (g := fun z => h z * inner ℝ z w) hgrad
      (hh.continuous.mul (continuous_id.inner continuous_const)).measurable A] at he
    exact he
  rw [integral_gaussianSmoothing_linearGradientPushforward (f := fun z => f z * inner ℝ z w)
      hgrad A
      (hf.continuous.mul (continuous_id.inner continuous_const)).measurable,
    integral_gaussianSmoothing_linearGradientPushforward (f := fun z => ‖gradient f z‖ ^ 2)
      hgrad A
      ((measurable_gradient f).norm.pow_const 2)]
  exact integral_gaussian_additive_stein_sq_le hXm hX2 hT2 w hs hf hc r

end MomentMap

theorem quadratic_gradient_dual_of_smoothed_raw_momentMap_C11 {n : ℕ}
    {φ V : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 1 φ) (hiso : IsIsotropic (MomentMap.gradientPushforward φ))
    (A : Matrix (Fin n) (Fin n) ℝ) (r : ℝ)
    (hpush : gaussianSmoothing (MomentMap.linearGradientPushforward φ A) r = potentialMeasure V)
    {G : ℝ≥0} (hG : LipschitzWith G (gradient φ))
    (U : Matrix (Fin n) (Fin n) ℝ) (hU : U.IsSymm) (i : Fin n) :
    CoordinateGradientDualBound V (matrixQuadratic U) i
      (4 * ∫ x, ‖MomentMap.rawTransportedHessianDerivative φ A x (WithLp.toLp 2 (U i)) +
        r ^ 2 • WithLp.toLp 2 (U i)‖ ^ 2 ∂potentialMeasure φ) := by
  intro h hh hc
  have hb := MomentMap.integral_smoothed_linear_target_sq_le_raw_stein_energy_C11
    hφ hiso hG hh hc A (WithLp.toLp 2 (U i)) r
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

theorem quadratic_variance_le_smoothed_raw_momentMap_energy_C11 {n : ℕ}
    {φ V : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
    [IsProbabilityMeasure (potentialMeasure V)]
    (hφ : ContDiff ℝ 1 φ) (hiso : IsIsotropic (MomentMap.gradientPushforward φ))
    (hV : ContDiff ℝ 2 V) (hconv : ConvexOn ℝ univ V)
    (A : Matrix (Fin n) (Fin n) ℝ) (r : ℝ)
    (hpush : gaussianSmoothing (MomentMap.linearGradientPushforward φ A) r = potentialMeasure V)
    {G : ℝ≥0} (hG : LipschitzWith G (gradient φ))
    (U : Matrix (Fin n) (Fin n) ℝ) (hU : U.IsSymm)
    (hq : MemLp (matrixQuadratic U) 2 (potentialMeasure V)) :
    ProbabilityTheory.variance (matrixQuadratic U) (potentialMeasure V) ≤
      4 * ∑ i : Fin n, ∫ x,
        ‖MomentMap.rawTransportedHessianDerivative φ A x (WithLp.toLp 2 (U i)) +
          r ^ 2 • WithLp.toLp 2 (U i)‖ ^ 2 ∂potentialMeasure φ := by
  rw [Finset.mul_sum]
  exact variance_le_sum_gradient_dual_smooth hV hconv
    ((contDiff_matrixQuadratic U).of_le (by simp)) hq
    (fun i => mul_nonneg (by norm_num) (integral_nonneg fun _ => sq_nonneg _))
    (quadratic_gradient_dual_of_smoothed_raw_momentMap_C11 hφ hiso A r hpush hG U hU)

end KLS
end

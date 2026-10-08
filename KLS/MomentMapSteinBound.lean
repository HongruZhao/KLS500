import KLS.MomentMapStein
import KLS.LocalRademacher
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Energy-dual bound from the actual moment-map Stein coupling

Cauchy--Schwarz bounds the linear functional on compact smooth tests by the
second moment of the genuine gradient derivative. This is the concrete
Stein-kernel contribution to Letwin's H^-1 step; no H^-1 variance theorem or
moment-map existence is assumed.
-/

open MeasureTheory InnerProductSpace Filter
open scoped BigOperators ContDiff

noncomputable section
namespace KLS

lemma integral_inner_sq_le {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {μ : Measure Ω}
    {f g : Ω → E} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, inner ℝ (f x) (g x) ∂μ) ^ 2 ≤
      (∫ x, ‖f x‖ ^ 2 ∂μ) * (∫ x, ‖g x‖ ^ 2 ∂μ) := by
  have hc := real_inner_mul_inner_self_le (hf.toLp f) (hg.toLp g)
  have hfg : inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, inner ℝ (f x) (g x) ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
    rw [hx, hy]
  have hff : inner ℝ (hf.toLp f) (hf.toLp f) = ∫ x, ‖f x‖ ^ 2 ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with x hx
    rw [hx, real_inner_self_eq_norm_sq]
  have hgg : inner ℝ (hg.toLp g) (hg.toLp g) = ∫ x, ‖g x‖ ^ 2 ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hg.coeFn_toLp] with x hx
    rw [hx, real_inner_self_eq_norm_sq]
  simpa only [hfg, hff, hgg, pow_two] using hc

namespace MomentMap
variable {n : ℕ}

lemma memLp_comp_gradient_test_gradient {φ f : Space n → ℝ}
    [IsFiniteMeasure (potentialMeasure φ)]
    (hgrad : Continuous (gradient φ)) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    MemLp (fun x => gradient f (gradient φ x)) 2 (potentialMeasure φ) := by
  obtain ⟨C, hC⟩ := (hc.fderiv ℝ).exists_bound_of_continuous
    (hf.fderiv_right (m := 0) (by norm_num)).continuous
  apply MemLp.of_bound ((measurable_gradient f).comp hgrad.measurable).aestronglyMeasurable C
  exact Eventually.of_forall fun x => by simpa only [Function.comp_def, norm_gradient_eq_norm_fderiv] using hC (gradient φ x)

lemma memLp_gradient_derivative_of_bound {φ : Space n → ℝ}
    [IsFiniteMeasure (potentialMeasure φ)]
    (hgrad : ContDiff ℝ 1 (gradient φ)) {M : ℝ}
    (hM : ∀ x, ‖fderiv ℝ (gradient φ) x‖ ≤ M) (v : Space n) :
    MemLp (fun x => fderiv ℝ (gradient φ) x v) 2 (potentialMeasure φ) := by
  have hm : Continuous (fun x => fderiv ℝ (gradient φ) x v) :=
    (hgrad.fderiv_right (m := 0) (by norm_num)).continuous.clm_apply continuous_const
  apply MemLp.of_bound hm.aestronglyMeasurable (M * ‖v‖)
  exact Eventually.of_forall fun x => (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _))

/-- Exact squared energy-dual bound in the genuine gradient coupling. -/
theorem integral_linear_test_sq_le_stein_energy {φ f : Space n → ℝ}
    [IsFiniteMeasure (potentialMeasure φ)]
    (hφ : Differentiable ℝ φ) (hgrad : ContDiff ℝ 1 (gradient φ))
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) {M : ℝ}
    (hM : ∀ x, ‖fderiv ℝ (gradient φ) x‖ ≤ M) (v : Space n) :
    (∫ z, f z * inner ℝ z v ∂gradientPushforward φ) ^ 2 ≤
      (∫ x, ‖fderiv ℝ (gradient φ) x v‖ ^ 2 ∂potentialMeasure φ) *
        (∫ z, ‖gradient f z‖ ^ 2 ∂gradientPushforward φ) := by
  rw [integral_target_mul_test_eq_of_hasCompactSupport hφ hgrad hf hc hM v]
  have hE : (∫ z, ‖gradient f z‖ ^ 2 ∂gradientPushforward φ) =
      ∫ x, ‖gradient f (gradient φ x)‖ ^ 2 ∂potentialMeasure φ := by
    unfold gradientPushforward
    exact integral_map hgrad.continuous.measurable.aemeasurable
      (((measurable_gradient f).norm.pow_const 2).aestronglyMeasurable)
  rw [hE, mul_comm]
  exact integral_inner_sq_le (memLp_comp_gradient_test_gradient hgrad.continuous hf hc)
    (memLp_gradient_derivative_of_bound hgrad hM v)

end MomentMap
end KLS
end

#print axioms KLS.integral_inner_sq_le
#print axioms KLS.MomentMap.integral_linear_test_sq_le_stein_energy

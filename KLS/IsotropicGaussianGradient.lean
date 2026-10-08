import KLS.IsotropicGaussianDensity
import KLS.GaussianSmoothingGradient

/-!
# Linear target-gradient growth after isotropic normalization

The scalar chain rule transfers the actual logarithmic Gaussian derivative
bound to the finite smooth potential of the exactly isotropic law.
-/

open MeasureTheory InnerProductSpace Set Filter Metric
open scoped ENNReal ContDiff Topology RealInnerProductSpace

noncomputable section
namespace KLS

theorem norm_gradient_scalarTransformedPotential {n : ℕ} {V : Space n → ℝ}
    (hV : Differentiable ℝ V) (a : ℝ) (x : Space n) :
    ‖gradient (scalarTransformedPotential V a) x‖ =
      |a⁻¹| * ‖gradient V (a⁻¹ • x)‖ := by
  have hd := ((hV (a⁻¹ • x)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).const_smul a⁻¹)).sub_const (Real.log |(a ^ n)⁻¹|)
  change HasFDerivAt (scalarTransformedPotential V a)
    ((fderiv ℝ V (a⁻¹ • x)).comp (a⁻¹ • ContinuousLinearMap.id ℝ (Space n))) x at hd
  simp only [norm_gradient_eq_norm_fderiv, hd.fderiv, ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.comp_id, norm_smul, Real.norm_eq_abs]

theorem norm_gradient_isotropicGaussianPotential_le {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hc : IsCompact μ.support) {R : ℝ}
    (hR : μ.support ⊆ closedBall (0 : Space n) R) {r : ℝ} (hr : r ≠ 0) (x : Space n) :
    ‖gradient (isotropicGaussianPotential μ r) x‖ ≤
      (r⁻¹) ^ 2 * (gaussianNormalization r)⁻¹ * R +
        ((r⁻¹) ^ 2 * ((gaussianNormalization r)⁻¹) ^ 2) * ‖x‖ := by
  have ha : 0 ≤ (gaussianNormalization r)⁻¹ := (inv_pos.mpr (gaussianNormalization_pos r)).le
  rw [isotropicGaussianPotential,
    norm_gradient_scalarTransformedPotential
      ((gaussianSmoothedPotential_contDiff hc hr).differentiable (by simp)), abs_of_nonneg ha]
  calc
    (gaussianNormalization r)⁻¹ *
        ‖gradient (gaussianSmoothedPotential μ r) ((gaussianNormalization r)⁻¹ • x)‖ ≤
      (gaussianNormalization r)⁻¹ *
        ((r⁻¹) ^ 2 * (‖(gaussianNormalization r)⁻¹ • x‖ + R)) :=
      mul_le_mul_of_nonneg_left (norm_gradient_gaussianSmoothedPotential_le hc hR hr _) ha
    _ = _ := by rw [norm_smul, Real.norm_of_nonneg ha]; ring

/-- Nonnegative constants for the exact target potential, suitable for
transporting the target drift through a genuine moment-map representation. -/
theorem exists_linear_growth_isotropicGaussianPotential {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hc : IsCompact μ.support) {r : ℝ} (hr : r ≠ 0) :
    ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧
      ∀ x, ‖gradient (isotropicGaussianPotential μ r) x‖ ≤ a + b * ‖x‖ := by
  obtain ⟨R, hR, hsub⟩ := hc.isBounded.subset_closedBall_lt 0 (0 : Space n)
  refine ⟨(r⁻¹) ^ 2 * (gaussianNormalization r)⁻¹ * R,
    (r⁻¹) ^ 2 * ((gaussianNormalization r)⁻¹) ^ 2, ?_, ?_, ?_⟩
  · exact mul_nonneg (mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (gaussianNormalization_pos r).le)) hR.le
  · positivity
  · exact norm_gradient_isotropicGaussianPotential_le hc hsub hr

end KLS
end

#print axioms KLS.norm_gradient_scalarTransformedPotential
#print axioms KLS.norm_gradient_isotropicGaussianPotential_le
#print axioms KLS.exists_linear_growth_isotropicGaussianPotential

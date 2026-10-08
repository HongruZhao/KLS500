import KLS.GaussianSmoothing
import KLS.CompactKernelDerivative
import KLS.LocalRademacher

/-!
# Linear growth of the actual Gaussian-smoothed potential gradient

For source support in the radius-R ball, the derivative of the actual kernel
integral is bounded by `r^-2 (norm x+R)` times its density. Differentiating
the negative logarithm gives the stated growth estimate.
-/

open MeasureTheory InnerProductSpace Set Filter Metric
open scoped ENNReal ContDiff Topology RealInnerProductSpace

noncomputable section
namespace KLS

lemma gaussianPotential_eq_norm_sq {n : ℕ} (x : Space n) :
    gaussianPotential n x = ‖x‖ ^ 2 / 2 +
      n * Real.log (Real.sqrt (2 * Real.pi)) := by
  simp only [gaussianPotential, gaussianCoordinatePotential, Finset.sum_add_distrib,
    ← Finset.sum_div, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, EuclideanSpace.real_norm_sq_eq]

lemma scaledGaussianKernel_eq_norm_sq {n : ℕ} (r : ℝ) (x : Space n) :
    scaledGaussianKernel n r x = |(r ^ n)⁻¹| *
      Real.exp (-((r⁻¹) ^ 2 / 2 * ‖x‖ ^ 2 +
        n * Real.log (Real.sqrt (2 * Real.pi)))) := by
  rw [scaledGaussianKernel, gaussianPotential_eq_norm_sq, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs]
  congr 2
  ring

lemma scaledGaussianKernel_nonneg (n : ℕ) (r : ℝ) (x : Space n) :
    0 ≤ scaledGaussianKernel n r x := by
  unfold scaledGaussianKernel
  positivity

lemma fderiv_scaledGaussianKernel {n : ℕ} (r : ℝ) (x : Space n) :
    fderiv ℝ (scaledGaussianKernel n r) x =
      (-((r⁻¹) ^ 2 * scaledGaussianKernel n r x)) • innerSL ℝ x := by
  have he : scaledGaussianKernel n r = fun z : Space n => |(r ^ n)⁻¹| *
      Real.exp (-((r⁻¹) ^ 2 / 2 * ‖z‖ ^ 2 +
        n * Real.log (Real.sqrt (2 * Real.pi)))) :=
    funext (scaledGaussianKernel_eq_norm_sq r)
  have hd := (((((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul ((r⁻¹) ^ 2 / 2)).add_const
    (n * Real.log (Real.sqrt (2 * Real.pi)))).neg).exp).const_mul |(r ^ n)⁻¹|
  simp only [Pi.neg_apply] at hd
  rw [he, hd.fderiv]
  ext y
  simp only [smul_apply, neg_apply, smul_eq_mul]
  ring

lemma norm_fderiv_scaledGaussianKernel {n : ℕ} (r : ℝ) (x : Space n) :
    ‖fderiv ℝ (scaledGaussianKernel n r) x‖ =
      (r⁻¹) ^ 2 * scaledGaussianKernel n r x * ‖x‖ := by
  rw [fderiv_scaledGaussianKernel, norm_smul, norm_neg, innerSL_apply_norm,
    Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (scaledGaussianKernel_nonneg n r x))]

theorem norm_fderiv_gaussianSmoothedDensity_le {n : ℕ} {μ : Measure (Space n)}
    [IsFiniteMeasure μ] (hc : IsCompact μ.support) {R : ℝ}
    (hR : μ.support ⊆ closedBall (0 : Space n) R) (r : ℝ) (x : Space n) :
    ‖fderiv ℝ (gaussianSmoothedDensity μ r) x‖ ≤
      ((r⁻¹) ^ 2 * (‖x‖ + R)) * gaussianSmoothedDensity μ r x := by
  have hg : ContDiff ℝ 1 (scaledGaussianKernel n r) :=
    (scaledGaussianKernel_contDiff n r).of_le (by simp)
  have hd := hasFDerivAt_integral_translate_of_compact_support hc hg x
  change HasFDerivAt (gaussianSmoothedDensity μ r)
    (∫ y, fderiv ℝ (scaledGaussianKernel n r) (x - y) ∂μ) x at hd
  rw [hd.fderiv]
  have hDn : Integrable (fun y => ‖fderiv ℝ (scaledGaussianKernel n r) (x - y)‖) μ :=
    integrable_of_continuous_compact_support_measure hc
      ((hg.continuous_fderiv (by norm_num)).comp (continuous_const.sub continuous_id)).norm
  have hB := (integrable_scaledGaussianKernel_translate hc r x).const_mul
    ((r⁻¹) ^ 2 * (‖x‖ + R))
  calc
    ‖∫ y, fderiv ℝ (scaledGaussianKernel n r) (x - y) ∂μ‖ ≤
        ∫ y, ‖fderiv ℝ (scaledGaussianKernel n r) (x - y)‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, ((r⁻¹) ^ 2 * (‖x‖ + R)) * scaledGaussianKernel n r (x - y) ∂μ := by
      apply integral_mono_ae hDn hB
      filter_upwards [μ.support_mem_ae] with y hy
      have hyR : ‖y‖ ≤ R := by simpa using hR hy
      rw [norm_fderiv_scaledGaussianKernel]
      calc
        (r⁻¹) ^ 2 * scaledGaussianKernel n r (x - y) * ‖x - y‖ ≤
            (r⁻¹) ^ 2 * scaledGaussianKernel n r (x - y) * (‖x‖ + R) :=
          mul_le_mul_of_nonneg_left ((norm_sub_le x y).trans (by linarith))
            (mul_nonneg (sq_nonneg _) (scaledGaussianKernel_nonneg n r _))
        _ = _ := by ring
    _ = _ := integral_const_mul _ _

/-- The concrete logarithmic derivative has linear growth in the target point. -/
theorem norm_gradient_gaussianSmoothedPotential_le {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hc : IsCompact μ.support) {R : ℝ}
    (hR : μ.support ⊆ closedBall (0 : Space n) R) {r : ℝ} (hr : r ≠ 0) (x : Space n) :
    ‖gradient (gaussianSmoothedPotential μ r) x‖ ≤ (r⁻¹) ^ 2 * (‖x‖ + R) := by
  have hp := gaussianSmoothedDensity_pos hc hr x
  have hd := (((gaussianSmoothedDensity_contDiff hc r).differentiable
    (by simp) x).hasFDerivAt.log hp.ne').neg
  change HasFDerivAt (gaussianSmoothedPotential μ r)
    (-((gaussianSmoothedDensity μ r x)⁻¹ • fderiv ℝ (gaussianSmoothedDensity μ r) x)) x at hd
  rw [norm_gradient_eq_norm_fderiv, hd.fderiv, norm_neg, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr hp.le)]
  calc
    (gaussianSmoothedDensity μ r x)⁻¹ * ‖fderiv ℝ (gaussianSmoothedDensity μ r) x‖ ≤
        (gaussianSmoothedDensity μ r x)⁻¹ *
          (((r⁻¹) ^ 2 * (‖x‖ + R)) * gaussianSmoothedDensity μ r x) :=
      mul_le_mul_of_nonneg_left (norm_fderiv_gaussianSmoothedDensity_le hc hR r x)
        (inv_nonneg.mpr hp.le)
    _ = _ := by field_simp

end KLS
end

#print axioms KLS.fderiv_scaledGaussianKernel
#print axioms KLS.norm_fderiv_gaussianSmoothedDensity_le
#print axioms KLS.norm_gradient_gaussianSmoothedPotential_le

import KLS.WeightedBochnerDomain

/-! Global weighted integration by parts from actual L² gradient and diffusion
integrability, using expanding compact cutoffs with vanishing first derivatives. -/

open MeasureTheory InnerProductSpace Set Filter
open scoped ContDiff RealInnerProductSpace Topology

noncomputable section
namespace KLS
variable {n : ℕ}

/-- Expanding smooth compact cutoffs preserve the integral of every L¹ function. -/
theorem integral_smoothCutoff_mul_tendsto {μ : Measure (Space n)} {F : Space n → ℝ}
    (hF : Integrable F μ) :
    Tendsto (fun k => ∫ x, smoothCutoff n k x * F x ∂μ) atTop (𝓝 (∫ x, F x ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => ‖F x‖)
    (fun k => (smoothCutoff_contDiff k).continuous.aestronglyMeasurable.mul
      hF.aestronglyMeasurable) hF.norm
  · intro k
    filter_upwards [] with x
    simp only [Pi.mul_apply]
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (faithfulCutoff_bounds k x).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (faithfulCutoff_bounds k x).2
  · filter_upwards [] with x
    simpa only [one_mul, Pi.mul_apply] using (smoothCutoff_tendsto_one x).mul_const (F x)

/-- The pairing of two actual L² gradients is integrable. -/
theorem integrable_inner_gradients_of_square {μ : Measure (Space n)} {f q : Space n → ℝ}
    (hf : ContDiff ℝ 1 f) (hq : ContDiff ℝ 1 q)
    (hF : Integrable (fun x => ‖gradient f x‖ ^ 2) μ)
    (hQ : Integrable (fun x => ‖gradient q x‖ ^ 2) μ) :
    Integrable (fun x => inner ℝ (gradient q x) (gradient f x)) μ := by
  have hfn : MemLp (fun x => ‖gradient f x‖) 2 μ :=
    (memLp_two_iff_integrable_sq
      (continuous_gradient_of_contDiff hf).norm.aestronglyMeasurable).mpr hF
  have hqn : MemLp (fun x => ‖gradient q x‖) 2 μ :=
    (memLp_two_iff_integrable_sq
      (continuous_gradient_of_contDiff hq).norm.aestronglyMeasurable).mpr hQ
  apply (hqn.integrable_mul hfn).mono'
    ((continuous_gradient_of_contDiff hq).inner
      (continuous_gradient_of_contDiff hf)).aestronglyMeasurable
  exact Eventually.of_forall fun x => by
    simpa only [Real.norm_eq_abs, Pi.mul_apply] using abs_real_inner_le_norm (gradient q x) (gradient f x)

/-- Global integration by parts needs actual L² pairings only. No boundary or
growth condition is imposed on the potential or the differentiated function. -/
theorem integral_mul_weightedDiffusion_of_L2_domain {φ f q : Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hf : ContDiff ℝ 2 f) (hq : ContDiff ℝ 1 q)
    (hL : MemLp (weightedDiffusion φ f) 2 (potentialMeasure φ))
    (hq2 : MemLp q 2 (potentialMeasure φ))
    (hF : Integrable (fun x => ‖gradient f x‖ ^ 2) (potentialMeasure φ))
    (hQ : Integrable (fun x => ‖gradient q x‖ ^ 2) (potentialMeasure φ)) :
    (∫ x, q x * weightedDiffusion φ f x ∂potentialMeasure φ) =
      -(∫ x, inner ℝ (gradient q x) (gradient f x) ∂potentialMeasure φ) := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hfn : MemLp (fun x => ‖gradient f x‖) 2 (potentialMeasure φ) :=
    (memLp_two_iff_integrable_sq
      (continuous_gradient_of_contDiff hf1).norm.aestronglyMeasurable).mpr hF
  have hpair := integrable_inner_gradients_of_square hf1 hq hF hQ
  have hprod := hq2.integrable_mul hL
  have hW : Integrable (fun x => ‖q x‖ * ‖gradient f x‖) (potentialMeasure φ) :=
    hq2.norm.integrable_mul hfn
  obtain ⟨K, hK, hbound⟩ := smoothCutoff_gradient_bound (n := n)
  let c : ℕ → ℝ := fun k => cutoffScale k * K
  let D : ℕ → Space n → ℝ := fun k x => q x *
    inner ℝ (gradient (smoothCutoff n k) x) (gradient f x)
  have hb (k : ℕ) (x : Space n) : |D k x| ≤ c k * (‖q x‖ * ‖gradient f x‖) := by
    calc
      |D k x| = ‖q x‖ * |inner ℝ (gradient (smoothCutoff n k) x) (gradient f x)| := by
        simp only [D, abs_mul, Real.norm_eq_abs]
      _ ≤ ‖q x‖ * (‖gradient (smoothCutoff n k) x‖ * ‖gradient f x‖) :=
        mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (norm_nonneg _)
      _ ≤ ‖q x‖ * (c k * ‖gradient f x‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (hbound k x) (norm_nonneg _)) (norm_nonneg _)
      _ = _ := by ring
  have hD : Tendsto (fun k => ∫ x, D k x ∂potentialMeasure φ) atTop (𝓝 0) :=
    tendsto_integral_zero_of_vanishing_bound hW
      (by simpa only [c, zero_mul] using cutoffScale_tendsto_zero.mul_const K) hb
  have heq (k : ℕ) :
      (∫ x, smoothCutoff n k x * (q x * weightedDiffusion φ f x) ∂potentialMeasure φ) =
        -(∫ x, smoothCutoff n k x * inner ℝ (gradient q x) (gradient f x)
          ∂potentialMeasure φ) - ∫ x, D k x ∂potentialMeasure φ := by
    have hi := integral_mul_weightedDiffusion_of_hasCompactSupport_left hφ
      ((smoothCutoff_contDiff k).mul hq) hf (smoothCutoff_hasCompactSupport k).mul_right
    have hA : Integrable (fun x => smoothCutoff n k x *
        inner ℝ (gradient q x) (gradient f x)) (potentialMeasure φ) :=
      integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
        ((smoothCutoff_contDiff k).continuous.mul
          ((continuous_gradient_of_contDiff hq).inner (continuous_gradient_of_contDiff hf1)))
        (smoothCutoff_hasCompactSupport k).mul_right
    have hB : Integrable (D k) (potentialMeasure φ) :=
      (hW.const_mul (c k)).mono'
        (hq.continuous.mul ((continuous_gradient_of_contDiff
          ((smoothCutoff_contDiff k).of_le (by simp))).inner
            (continuous_gradient_of_contDiff hf1))).aestronglyMeasurable
        (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hb k x)
    have hgrad : (∫ x, inner ℝ (gradient (fun y => smoothCutoff n k y * q y) x)
        (gradient f x) ∂potentialMeasure φ) =
      (∫ x, smoothCutoff n k x * inner ℝ (gradient q x) (gradient f x) ∂potentialMeasure φ) +
        ∫ x, D k x ∂potentialMeasure φ := by
      rw [← integral_add hA hB]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        dsimp only
        rw [gradient_mul_real ((smoothCutoff_contDiff k).differentiable (by simp) x)
          (hq.differentiable (by norm_num) x)]
        simp only [inner_add_left, inner_smul_left, conj_trivial, D, Pi.add_apply]
        ring
    rw [hgrad] at hi
    simpa only [mul_assoc, neg_add_rev, sub_eq_add_neg, add_comm] using hi
  have hleft := integral_smoothCutoff_mul_tendsto hprod
  have hright := (integral_smoothCutoff_mul_tendsto hpair).neg.sub hD
  have ht : Tendsto
      (fun k => ∫ x, smoothCutoff n k x * (q x * weightedDiffusion φ f x) ∂potentialMeasure φ)
      atTop (𝓝 (-(∫ x, inner ℝ (gradient q x) (gradient f x) ∂potentialMeasure φ))) := by
    simpa only [← heq, sub_zero] using hright
  exact tendsto_nhds_unique hleft ht

end KLS
end

#print axioms KLS.integral_smoothCutoff_mul_tendsto
#print axioms KLS.integrable_inner_gradients_of_square
#print axioms KLS.integral_mul_weightedDiffusion_of_L2_domain

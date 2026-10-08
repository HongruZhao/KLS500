import KLS.CompactLipschitzDerivativeBounds

/-! Actual bounded mollifiers converge in every finite absolutely continuous weighted L2 space. -/
open MeasureTheory Set Filter ContinuousLinearMap
open scoped Topology ENNReal Convolution
noncomputable section
namespace KLS
variable {n : ℕ}

theorem norm_mollify_le_of_ae_bound {f : Space n → ℝ} {C : ℝ}
    (hb : ∀ᵐ x ∂volume, ‖f x‖ ≤ C) (k : ℕ) (x : Space n) :
    ‖mollify k f x‖ ≤ C := by
  have hi := ((mollifierBump n k).integrable_normed (μ := volume)).comp_sub_left x
  have he : (∫ y, C * mollifierKernel n k (x - y)) = C := by
    rw [integral_const_mul, integral_sub_left_eq_self]
    simp only [mollifierKernel, (mollifierBump n k).integral_normed, mul_one]
  unfold mollify scalarConvolution
  rw [convolution_def]
  calc
    ‖∫ y, (lsmul ℝ ℝ) (f y) (mollifierKernel n k (x - y))‖ ≤
        ∫ y, C * mollifierKernel n k (x - y) := by
      apply norm_integral_le_of_norm_le (hi.const_mul C)
      filter_upwards [hb] with y hy
      have hk : 0 ≤ mollifierKernel n k (x - y) := (mollifierBump n k).nonneg_normed _
      change |f y * mollifierKernel n k (x - y)| ≤ C * mollifierKernel n k (x-y)
      rw [abs_mul, abs_of_nonneg hk]
      exact mul_le_mul_of_nonneg_right hy hk
    _ = C := he

theorem bounded_mollify_weighted_L2_convergence {μ : Measure (Space n)} [IsFiniteMeasure μ]
    (hμ : μ ≪ volume) {f : Space n → ℝ} (hf : LocallyIntegrable f volume)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ x ∂volume, ‖f x‖ ≤ C) :
    (∀ k, MemLp (mollify k f) 2 μ) ∧ MemLp f 2 μ ∧
      Tendsto (fun k => eLpNorm (mollify k f - f) 2 μ) atTop (𝓝 0) := by
  have hbμ : ∀ᵐ x ∂μ, ‖f x‖ ≤ C := hμ.ae_le hb
  have hfμ : MemLp f 2 μ := (memLp_const C).mono'
    (hf.aestronglyMeasurable.mono_ac hμ)
    (hbμ.mono fun x hx => by simpa only [Real.norm_eq_abs, abs_of_nonneg hC] using hx)
  have hmk (k : ℕ) : MemLp (mollify k f) 2 μ := (memLp_const C).mono'
    ((mollify_contDiff hf k).continuous.aestronglyMeasurable)
    (Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg hC] using norm_mollify_le_of_ae_bound hb k x)
  refine ⟨hmk, hfμ, tendsto_eLpNorm_zero_of_integral_sq (fun k => (hmk k).sub hfμ) ?_⟩
  have hdom (k : ℕ) : ∀ᵐ x ∂μ, ‖(mollify k f x - f x) ^ 2‖ ≤ 4 * C ^ 2 := by
    filter_upwards [hbμ] with x hx
    have hm := norm_mollify_le_of_ae_bound hb k x
    rw [Real.norm_eq_abs] at hm hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hd : |mollify k f x - f x| ≤ 2*C :=
      (abs_sub _ _).trans (by linarith)
    have hs := (sq_le_sq₀ (abs_nonneg _) (show 0 ≤ 2*C by positivity)).mpr hd
    nlinarith [sq_abs (mollify k f x-f x)]
  have hpt : ∀ᵐ x ∂μ, Tendsto (fun k => mollify k f x) atTop (𝓝 (f x)) :=
    hμ.ae_le (mollify_tendsto_ae hf)
  have ht := tendsto_integral_of_dominated_convergence (fun _ : Space n => 4 * C ^ 2)
    (fun k => ((hmk k).aestronglyMeasurable.sub hfμ.aestronglyMeasurable).pow 2)
    (integrable_const _) hdom
    (hpt.mono fun x hx => by
      simpa only [Pi.pow_apply, Pi.sub_apply, sub_self, zero_pow (by norm_num : 2 ≠ 0)] using (hx.sub_const (f x)).pow 2)
  simpa only [integral_zero, Pi.sub_apply, Pi.pow_apply] using ht

end KLS
end

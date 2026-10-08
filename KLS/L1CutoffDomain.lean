import KLS.L1CutoffApproximation

open MeasureTheory Set Filter
open scoped Topology ENNReal

noncomputable section
namespace KLS
variable {n : ℕ}

theorem integrable_gradient_smoothCutoff_mul
    {μ : Measure (Space n)} (hμ : μ ≪ volume) {f : Space n → ℝ}
    (hf : LocallyLipschitz f) (hfi : Integrable f μ) (hgi : Integrable (gradient f) μ) (k : ℕ) :
    Integrable (gradient (fun x => smoothCutoff n k x * f x)) μ := by
  have hleft := hgi.bdd_smul 1
    (smoothCutoff_contDiff k).continuous.aestronglyMeasurable
    (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (faithfulCutoff_bounds k x).1]
      exact (faithfulCutoff_bounds k x).2)
  obtain ⟨K, _, hb⟩ := smoothCutoff_gradient_bound (n := n)
  have hright := hfi.smul_bdd (cutoffScale k * K)
    (measurable_gradient _).aestronglyMeasurable (Eventually.of_forall (hb k))
  exact (hleft.add hright).congr (gradient_smoothCutoff_mul_ae hμ hf k).symm

theorem lintegral_abs_smoothCutoff_mul_sub_tendsto_zero
    {μ : Measure (Space n)} {f : Space n → ℝ} (hf : Integrable f μ) :
    Tendsto (fun k => ∫⁻ x, ENNReal.ofReal |smoothCutoff n k x * f x - f x| ∂μ)
      atTop (𝓝 0) := by
  have ht := (ENNReal.continuous_ofReal.tendsto 0).comp
    (integral_abs_smoothCutoff_mul_sub_tendsto_zero hf)
  have he (k : ℕ) : ENNReal.ofReal (∫ x, |smoothCutoff n k x * f x - f x| ∂μ) =
      ∫⁻ x, ENNReal.ofReal |smoothCutoff n k x * f x - f x| ∂μ :=
    ofReal_integral_eq_lintegral_ofReal ((integrable_smoothCutoff_mul hf k).sub hf).abs
      (Eventually.of_forall fun x => abs_nonneg (smoothCutoff n k x * f x - f x))
  simpa only [Function.comp_def, ENNReal.ofReal_zero, he] using ht

theorem lintegral_norm_gradient_smoothCutoff_mul_sub_tendsto_zero
    {μ : Measure (Space n)} (hμ : μ ≪ volume) {f : Space n → ℝ}
    (hf : LocallyLipschitz f) (hfi : Integrable f μ) (hgi : Integrable (gradient f) μ) :
    Tendsto (fun k => ∫⁻ x,
      ENNReal.ofReal ‖gradient (fun y => smoothCutoff n k y * f y) x - gradient f x‖ ∂μ)
      atTop (𝓝 0) := by
  have ht := (ENNReal.continuous_ofReal.tendsto 0).comp
    (integral_norm_gradient_smoothCutoff_mul_sub_tendsto_zero hμ hf hfi hgi)
  have he (k : ℕ) : ENNReal.ofReal (∫ x,
      ‖gradient (fun y => smoothCutoff n k y * f y) x - gradient f x‖ ∂μ) =
      ∫⁻ x, ENNReal.ofReal ‖gradient (fun y => smoothCutoff n k y * f y) x - gradient f x‖ ∂μ :=
    ofReal_integral_eq_lintegral_ofReal
      ((integrable_gradient_smoothCutoff_mul hμ hf hfi hgi k).sub hgi).norm
      (Eventually.of_forall fun x => norm_nonneg
        (gradient (fun y => smoothCutoff n k y * f y) x - gradient f x))
  simpa only [Function.comp_def, ENNReal.ofReal_zero, he] using ht

theorem integral_norm_gradient_smoothCutoff_mul_tendsto
    {μ : Measure (Space n)} (hμ : μ ≪ volume) {f : Space n → ℝ}
    (hf : LocallyLipschitz f) (hfi : Integrable f μ) (hgi : Integrable (gradient f) μ) :
    Tendsto (fun k => ∫ x, ‖gradient (fun y => smoothCutoff n k y * f y) x‖ ∂μ)
      atTop (𝓝 (∫ x, ‖gradient f x‖ ∂μ)) := by
  apply tendsto_integral_of_L1 (fun x => ‖gradient f x‖) hgi.norm.aestronglyMeasurable
    (Eventually.of_forall fun k => (integrable_gradient_smoothCutoff_mul hμ hf hfi hgi k).norm)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (lintegral_norm_gradient_smoothCutoff_mul_sub_tendsto_zero hμ hf hfi hgi)
    (fun _ => zero_le) (fun k => lintegral_mono fun x => ?_)
  rw [← ofReal_norm]
  apply ENNReal.ofReal_le_ofReal
  simpa only [Real.norm_eq_abs] using abs_norm_sub_norm_le
    (gradient (fun y => smoothCutoff n k y * f y) x) (gradient f x)

end KLS
end

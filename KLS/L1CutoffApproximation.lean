import KLS.WeightedFaithfulCutoff

open MeasureTheory Set Filter
open scoped Topology ENNReal

noncomputable section
namespace KLS
variable {n : ℕ}

lemma smoothCutoff_gradient_tendsto_zero (x : Space n) :
    Tendsto (fun k => gradient (smoothCutoff n k) x) atTop (𝓝 0) := by
  obtain ⟨K, _, hb⟩ := smoothCutoff_gradient_bound (n := n)
  apply squeeze_zero_norm (fun k => hb k x)
  simpa using cutoffScale_tendsto_zero.mul_const K

lemma gradient_smoothCutoff_mul_ae {μ : Measure (Space n)} (hμ : μ ≪ volume)
    {f : Space n → ℝ} (hf : LocallyLipschitz f) (k : ℕ) :
    gradient (fun x => smoothCutoff n k x * f x) =ᵐ[μ]
      fun x => smoothCutoff n k x • gradient f x + f x • gradient (smoothCutoff n k) x := by
  filter_upwards [locallyLipschitz_ae_differentiableAt_of_absolutelyContinuous hμ hf] with x hx
  rw [gradient_mul_real ((smoothCutoff_contDiff k).differentiable (by norm_num) x) hx]
  exact add_comm _ _

lemma integrable_smoothCutoff_mul {μ : Measure (Space n)} {f : Space n → ℝ}
    (hf : Integrable f μ) (k : ℕ) : Integrable (fun x => smoothCutoff n k x * f x) μ := by
  apply hf.norm.mono'
    ((smoothCutoff_contDiff k).continuous.aestronglyMeasurable.mul hf.aestronglyMeasurable)
  exact Eventually.of_forall fun x => by
    change ‖smoothCutoff n k x * f x‖ ≤ ‖f x‖
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (faithfulCutoff_bounds k x).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (faithfulCutoff_bounds k x).2

/-- The actual compact spatial cutoffs approximate every integrable function in L1. -/
theorem integral_abs_smoothCutoff_mul_sub_tendsto_zero
    {μ : Measure (Space n)} {f : Space n → ℝ} (hf : Integrable f μ) :
    Tendsto (fun k => ∫ x, |smoothCutoff n k x * f x - f x| ∂μ) atTop (𝓝 0) := by
  have hm (k : ℕ) : AEStronglyMeasurable
      (fun x => |smoothCutoff n k x * f x - f x|) μ := by
    simpa only [Pi.sub_apply, Pi.mul_apply, Real.norm_eq_abs] using
      (((smoothCutoff_contDiff k).continuous.aestronglyMeasurable.mul hf.aestronglyMeasurable).sub
        hf.aestronglyMeasurable).norm
  have hb (k : ℕ) (x : Space n) : |smoothCutoff n k x * f x - f x| ≤ |f x| := by
    have hχ := faithfulCutoff_bounds k x
    calc
      _ = |smoothCutoff n k x - 1| * |f x| := by rw [← abs_mul]; congr 1; ring
      _ ≤ 1 * |f x| := mul_le_mul_of_nonneg_right (by rw [abs_le]; constructor <;> linarith) (abs_nonneg _)
      _ = _ := one_mul _
  have ht := tendsto_integral_of_dominated_convergence (fun x => |f x|) hm hf.abs
    (fun k => Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs, abs_abs] using hb k x)
    (Eventually.of_forall fun x => by
      simpa using (((smoothCutoff_tendsto_one x).mul_const (f x)).sub_const (f x)).abs)
  simpa only [integral_zero] using ht

/-- Actual gradients of compact cutoffs approximate an integrable actual gradient
in L1. Only absolute continuity of the measure and the original L1 data are used. -/
theorem integral_norm_gradient_smoothCutoff_mul_sub_tendsto_zero
    {μ : Measure (Space n)} (hμ : μ ≪ volume) {f : Space n → ℝ}
    (hf : LocallyLipschitz f) (hfi : Integrable f μ) (hgi : Integrable (gradient f) μ) :
    Tendsto (fun k => ∫ x,
      ‖gradient (fun y => smoothCutoff n k y * f y) x - gradient f x‖ ∂μ)
      atTop (𝓝 0) := by
  let F (k : ℕ) (x : Space n) := gradient (fun y => smoothCutoff n k y * f y) x - gradient f x
  have hm (k : ℕ) : AEStronglyMeasurable (F k) μ :=
    ((measurable_gradient _).sub (measurable_gradient _)).aestronglyMeasurable
  obtain ⟨K, hK, hb⟩ := smoothCutoff_gradient_bound (n := n)
  have hKu (k : ℕ) (x : Space n) : ‖gradient (smoothCutoff n k) x‖ ≤ K := by
    refine (hb k x).trans ?_
    apply mul_le_of_le_one_left hK
    unfold cutoffScale
    apply inv_le_one_of_one_le₀
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have heq (k : ℕ) : F k =ᵐ[μ] fun x =>
      (smoothCutoff n k x - 1) • gradient f x + f x • gradient (smoothCutoff n k) x := by
    filter_upwards [gradient_smoothCutoff_mul_ae hμ hf k] with x hx
    dsimp only [F]
    rw [hx, sub_smul, one_smul]
    abel
  have hbound (k : ℕ) : ∀ᵐ x ∂μ, ‖F k x‖ ≤ ‖gradient f x‖ + K * |f x| := by
    filter_upwards [heq k] with x hx
    rw [hx]
    apply (norm_add_le _ _).trans
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    have hχ := faithfulCutoff_bounds k x
    have hd : |smoothCutoff n k x - 1| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    exact add_le_add (mul_le_of_le_one_left (norm_nonneg _) hd)
      ((mul_le_mul_of_nonneg_left (hKu k x) (abs_nonneg _)).trans_eq (mul_comm _ _))
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun k => ‖F k x‖) atTop (𝓝 0) := by
    filter_upwards [ae_all_iff.mpr heq] with x hx
    have ht := (((smoothCutoff_tendsto_one x).sub_const 1).smul_const (gradient f x)).add
      ((smoothCutoff_gradient_tendsto_zero x).const_smul (f x))
    simpa only [hx, sub_self, zero_smul, smul_zero, zero_add, norm_zero] using ht.norm
  have ht := tendsto_integral_of_dominated_convergence
    (fun x => ‖gradient f x‖ + K * |f x|) (fun k => (hm k).norm)
    (hgi.norm.add (hfi.abs.const_mul K))
    (fun k => by simpa only [Real.norm_eq_abs, abs_norm] using hbound k) hlim
  simpa only [integral_zero] using ht

end KLS
end

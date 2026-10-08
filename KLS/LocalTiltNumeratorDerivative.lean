import KLS.LocalNormExponentialDomain

open MeasureTheory InnerProductSpace Set Filter Metric
open scoped ContDiff Topology BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

theorem hasFDerivAt_tiltNumerator_of_localNormExponentialDomain
    {μ : Measure (Space n)} {f : Space n → ℝ} {r : ℝ}
    (hf : LocalNormExponentialDomain μ f r) {z : Space n} (hz : ‖z‖ < r) :
    HasFDerivAt (tiltNumerator μ (fun _ => 0) f)
      (∫ x, (f x * Real.exp (inner ℝ z x)) • innerSL ℝ x ∂μ) z := by
  have hnum : tiltNumerator μ (fun _ => 0) f =
      fun w => ∫ x, f x * Real.exp (inner ℝ w x) ∂μ := by
    funext w
    simp only [tiltNumerator, zero_add]
  rw [hnum]
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := fun w x => (f x * Real.exp (inner ℝ w x)) • innerSL ℝ x)
    (s := ball z (r - ‖z‖)) (bound := fun x => ‖f x‖ * ‖x‖ ^ 1 * Real.exp (r * ‖x‖))
    (ball_mem_nhds z (sub_pos.mpr hz))
    (Eventually.of_forall (fun w => hf.1.mul
      (show Continuous (fun x : Space n => Real.exp (inner ℝ w x)) by fun_prop).aestronglyMeasurable))
    (hf.integrable_tilt hz.le) (hf.integrable_tilt_derivative hz.le).aestronglyMeasurable
  · filter_upwards [] with x
    intro w hw
    change ‖(f x * Real.exp (inner ℝ w x)) • innerSL ℝ x‖ ≤ _
    have hw' : ‖w‖ ≤ r := by
      have hd : ‖w - z‖ < r - ‖z‖ := by simpa only [mem_ball, dist_eq_norm] using hw
      have hn := norm_add_le (w-z) z
      have he : (w-z)+z = w := by abel
      rw [he] at hn
      linarith
    have he : Real.exp (inner ℝ w x) ≤ Real.exp (r * ‖x‖) :=
      (exp_inner_le_exp_norm w x).trans (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right hw' (norm_nonneg x)))
    simp only [norm_smul, norm_mul, innerSL_apply_norm, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), pow_one]
    calc
      _ ≤ |f x| * Real.exp (r * ‖x‖) * ‖x‖ := by gcongr
      _ = _ := by ring
  · exact hf.2 1
  · exact Eventually.of_forall fun x w _ => by
      simpa only [Pi.mul_apply, innerSL_apply_apply, real_inner_comm x, mul_smul] using
        (((innerSL ℝ x).hasFDerivAt).exp).const_mul (f x)

theorem hasFDerivAt_tiltNumerator_coordinate_of_localNormExponentialDomain
    {μ : Measure (Space n)} {f : Space n → ℝ} {r : ℝ}
    (hf : LocalNormExponentialDomain μ f r) {z : Space n} (hz : ‖z‖ < r) :
    HasFDerivAt (tiltNumerator μ (fun _ => 0) f)
      (∑ i, tiltNumerator μ (fun _ => 0) (fun x => f x * x i) z •
        (EuclideanSpace.proj i : Space n →L[ℝ] ℝ)) z := by
  convert hasFDerivAt_tiltNumerator_of_localNormExponentialDomain hf hz using 1
  ext y
  rw [ContinuousLinearMap.integral_apply (hf.integrable_tilt_derivative hz.le)]
  simp only [_root_.sum_apply, _root_.smul_apply, EuclideanSpace.coe_proj, smul_eq_mul,
    innerSL_apply_apply, tiltNumerator, zero_add]
  simp_rw [inner_eq_coordinate_sum (u := y), Finset.mul_sum]
  have hi (i : Fin n) : Integrable (fun x => f x * Real.exp (inner ℝ z x) * (y i * x i)) μ := by
    convert ((hf.mul_coordinate i).integrable_tilt hz.le).mul_const (y i) using 1
    funext x
    ring
  rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [← integral_mul_const]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by ring

end KLS
end

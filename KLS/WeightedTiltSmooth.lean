import KLS.NormExponentialDomain

/-! Smoothness of the actual normalized tilt for every weighted L² observable.
Every local derivative envelope is derived from genuine radial exponential
moments, and coordinate multiplication preserves the concrete moment domain. -/

open MeasureTheory InnerProductSpace Set Filter Metric Matrix
open scoped ContDiff RealInnerProductSpace Topology BigOperators

noncomputable section
namespace KLS
variable {n : ℕ}

theorem hasFDerivAt_tiltNumerator_of_normExponentialDomain
    {μ : Measure (Space n)} {f : Space n → ℝ}
    (hf : NormExponentialDomain μ f) (z : Space n) :
    HasFDerivAt (tiltNumerator μ (fun _ => 0) f)
      (∫ x, (f x * Real.exp (inner ℝ z x)) • innerSL ℝ x ∂μ) z := by
  have hnum : tiltNumerator μ (fun _ => 0) f =
      fun w => ∫ x, f x * Real.exp (inner ℝ w x) ∂μ := by
    funext w
    simp only [tiltNumerator, zero_add]
  rw [hnum]
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := fun w x => (f x * Real.exp (inner ℝ w x)) • innerSL ℝ x)
    (s := ball z 1) (bound := fun x => ‖f x‖ * ‖x‖ ^ 1 * Real.exp ((‖z‖ + 1) * ‖x‖))
    (ball_mem_nhds z zero_lt_one)
    (Eventually.of_forall (fun w => (hf.integrable_tilt w).aestronglyMeasurable))
    (hf.integrable_tilt z) (hf.integrable_tilt_derivative z).aestronglyMeasurable
  · filter_upwards [] with x
    intro w hw
    change ‖(f x * Real.exp (inner ℝ w x)) • innerSL ℝ x‖ ≤ _
    have hw' : ‖w‖ ≤ ‖z‖ + 1 := by
      have hd : ‖w - z‖ < 1 := by simpa only [mem_ball, dist_eq_norm] using hw
      calc
        ‖w‖ = ‖(w - z) + z‖ := by congr 1; abel
        _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
        _ ≤ ‖z‖ + 1 := by linarith
    have he : Real.exp (inner ℝ w x) ≤ Real.exp ((‖z‖ + 1) * ‖x‖) :=
      (exp_inner_le_exp_norm w x).trans (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right hw' (norm_nonneg x)))
    simp only [norm_smul, norm_mul, innerSL_apply_norm, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), pow_one]
    calc
      _ ≤ |f x| * Real.exp ((‖z‖ + 1) * ‖x‖) * ‖x‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (abs_nonneg _)) (norm_nonneg _)
      _ = _ := by ring
  · exact hf.2 1 (‖z‖ + 1)
  · exact Eventually.of_forall fun x w _ => by
      simpa only [innerSL_apply_apply, real_inner_comm x, mul_smul] using
        (((innerSL ℝ x).hasFDerivAt).exp).const_mul (f x)

theorem hasFDerivAt_tiltNumerator_coordinate_of_normExponentialDomain
    {μ : Measure (Space n)} {f : Space n → ℝ}
    (hf : NormExponentialDomain μ f) (z : Space n) :
    HasFDerivAt (tiltNumerator μ (fun _ => 0) f)
      (∑ i, tiltNumerator μ (fun _ => 0) (fun x => f x * x i) z •
        (EuclideanSpace.proj i : Space n →L[ℝ] ℝ)) z := by
  convert hasFDerivAt_tiltNumerator_of_normExponentialDomain hf z using 1
  ext y
  rw [ContinuousLinearMap.integral_apply (hf.integrable_tilt_derivative z)]
  simp only [_root_.sum_apply, _root_.smul_apply, EuclideanSpace.coe_proj, smul_eq_mul,
    innerSL_apply_apply, tiltNumerator, zero_add]
  simp_rw [inner_eq_coordinate_sum (u := y), Finset.mul_sum]
  have hi (i : Fin n) : Integrable (fun x => f x * Real.exp (inner ℝ z x) * (y i * x i)) μ := by
    convert ((hf.mul_coordinate i).integrable_tilt z).mul_const (y i) using 1
    funext x
    ring
  rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [← integral_mul_const]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by ring

theorem contDiff_tiltNumerator_nat_of_normExponentialDomain
    {μ : Measure (Space n)} {f : Space n → ℝ}
    (hf : NormExponentialDomain μ f) (k : ℕ) :
    ContDiff ℝ k (tiltNumerator μ (fun _ => 0) f) := by
  induction k generalizing f with
  | zero =>
    rw [Nat.cast_zero, contDiff_zero]
    exact Differentiable.continuous (fun z =>
      (hasFDerivAt_tiltNumerator_coordinate_of_normExponentialDomain hf z).differentiableAt)
  | succ k ih =>
    rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_fderiv]
    refine ⟨fun z => (hasFDerivAt_tiltNumerator_coordinate_of_normExponentialDomain hf z).differentiableAt,
      by simp, ?_⟩
    have he : fderiv ℝ (tiltNumerator μ (fun _ => 0) f) =
        fun z => ∑ i, tiltNumerator μ (fun _ => 0) (fun x => f x * x i) z •
          (EuclideanSpace.proj i : Space n →L[ℝ] ℝ) :=
      funext (fun z => (hasFDerivAt_tiltNumerator_coordinate_of_normExponentialDomain hf z).fderiv)
    rw [he]
    apply ContDiff.sum
    intro i _
    exact (ih (hf.mul_coordinate i)).smul contDiff_const

theorem contDiff_tiltNumerator_of_normExponentialDomain
    {μ : Measure (Space n)} {f : Space n → ℝ} (hf : NormExponentialDomain μ f) :
    ContDiff ℝ (⊤ : ℕ∞) (tiltNumerator μ (fun _ => 0) f) :=
  contDiff_infty.mpr (contDiff_tiltNumerator_nat_of_normExponentialDomain hf)

theorem contDiff_exponentialTilt_average_of_weighted_memLp
    {φ f : Space n → ℝ} {κ : ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ y (v : Fin n → ℝ),
      κ * (v ⬝ᵥ v) ≤ v ⬝ᵥ (coordinateHessian φ y *ᵥ v))
    (hf : MemLp f 2 (potentialMeasure φ)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => ∫ x, f x ∂exponentialTilt (potentialMeasure φ) z) := by
  have hD := normExponentialDomain_of_memLp_potentialMeasure hφ hκ hlower hf
  have hD1 := normExponentialDomain_of_memLp_potentialMeasure hφ hκ hlower
    (memLp_const (μ := potentialMeasure φ) (p := 2) (1 : ℝ))
  change ContDiff ℝ (⊤ : ℕ∞) (fun z => tiltAverage (potentialMeasure φ) (fun x => inner ℝ z x) f)
  simp_rw [tiltAverage_eq_ratio]
  have hN : ContDiff ℝ (⊤ : ℕ∞) (fun z => ∫ x, f x * Real.exp (inner ℝ z x) ∂potentialMeasure φ) := by
    convert contDiff_tiltNumerator_of_normExponentialDomain hD using 1
    funext z
    simp only [tiltNumerator, zero_add]
  have hZ : ContDiff ℝ (⊤ : ℕ∞) (fun z => tiltPartition (potentialMeasure φ) (fun x => inner ℝ z x)) := by
    convert contDiff_tiltNumerator_of_normExponentialDomain hD1 using 1
    funext z
    simp only [tiltNumerator, tiltPartition, zero_add, one_mul]
  exact hN.div hZ (fun z => (integral_exp_pos
    (integrable_exp_inner_potentialMeasure hφ hκ hlower z)).ne')

end KLS
end

#print axioms KLS.hasFDerivAt_tiltNumerator_of_normExponentialDomain
#print axioms KLS.contDiff_tiltNumerator_of_normExponentialDomain
#print axioms KLS.contDiff_exponentialTilt_average_of_weighted_memLp

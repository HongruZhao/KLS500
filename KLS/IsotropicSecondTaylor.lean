import KLS.WeightedTaylorFirstMoment
import KLS.TiltNumeratorMoments
import KLS.HessianMetricProduct

open MeasureTheory InnerProductSpace Matrix Filter
open scoped ContDiff RealInnerProductSpace BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

lemma coordinateHessian_tiltNumerator_zero_of_normExponentialDomain
    {μ : Measure (Space n)} {f : Space n → ℝ} (hf : NormExponentialDomain μ f)
    (i j : Fin n) :
    coordinateHessian (tiltNumerator μ (fun _ => 0) f) 0 i j =
      ∫ x, f x * (x i * x j) ∂μ := by
  have hs := contDiff_tiltNumerator_of_normExponentialDomain hf
  have hd := ((hs.of_le (by simp) : ContDiff ℝ 2 _).fderiv_right
    (m := 1) (by norm_num)).differentiable (by norm_num) (0 : Space n)
  have hh := iteratedFDeriv_tiltNumerator_moment hf 0
    ![EuclideanSpace.single i 1, EuclideanSpace.single j 1]
  rw [coordinateHessian_eq_fderiv_fderiv hd]
  simpa only [iteratedFDeriv_two_apply, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Fin.prod_univ_two,
    EuclideanSpace.inner_single_right, RCLike.conj_to_real, one_mul,
    inner_zero_left, Real.exp_zero, mul_one] using hh

lemma coordinateDerivative_tiltNumerator_zero_of_normExponentialDomain
    {μ : Measure (Space n)} {f : Space n → ℝ} (hf : NormExponentialDomain μ f)
    (i : Fin n) :
    coordinateDerivative (tiltNumerator μ (fun _ => 0) f) i 0 =
      ∫ x, f x * x i ∂μ := by
  unfold coordinateDerivative
  rw [(hasFDerivAt_tiltNumerator_coordinate_of_normExponentialDomain hf 0).fderiv]
  simp [tiltNumerator]

/-- The actual Hessian of the normalized exponential-tilt average at zero is
its centered second coordinate moment for an isotropic law. -/
theorem coordinateHessian_exponentialTilt_average_zero_of_isotropic
    {V f : Space n → ℝ} {κ : ℝ} [IsProbabilityMeasure (potentialMeasure V)]
    (hV : ContDiff ℝ 2 V) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian V x *ᵥ a))
    (hiso : IsIsotropic (potentialMeasure V)) (hf : MemLp f 2 (potentialMeasure V))
    (i j : Fin n) :
    coordinateHessian (fun z => ∫ x, f x ∂exponentialTilt (potentialMeasure V) z) 0 i j =
      (∫ x, f x * (x i * x j) ∂potentialMeasure V) -
        (∫ x, f x ∂potentialMeasure V) * (if i = j then 1 else 0) := by
  let N := tiltNumerator (potentialMeasure V) (fun _ => 0) f
  let Z := tiltNumerator (potentialMeasure V) (fun _ => 0) (fun _ => 1)
  let A := fun z => ∫ x, f x ∂exponentialTilt (potentialMeasure V) z
  have hD := normExponentialDomain_of_memLp_potentialMeasure hV hκ hlower hf
  have hD1 := normExponentialDomain_of_memLp_potentialMeasure hV hκ hlower
    (memLp_const (μ := potentialMeasure V) (p := 2) (1 : ℝ))
  have hA : ContDiff ℝ 2 A :=
    (contDiff_exponentialTilt_average_of_weighted_memLp hV hκ hlower hf).of_le (by simp)
  have hZ : ContDiff ℝ 2 Z :=
    (contDiff_tiltNumerator_of_normExponentialDomain hD1).of_le (by simp)
  have heq : (fun z => A z * Z z) = N := by
    funext z
    have hz : Z z ≠ 0 := by
      change (∫ x, 1 * Real.exp (0 + inner ℝ z x) ∂potentialMeasure V) ≠ 0
      simpa only [one_mul, zero_add] using
        (integral_exp_pos (integrable_exp_inner_potentialMeasure hV hκ hlower z)).ne'
    change tiltAverage (potentialMeasure V) (fun x => inner ℝ z x) f * Z z = N z
    rw [tiltAverage_eq_ratio]
    simpa only [N, Z, tiltNumerator, tiltPartition, zero_add, one_mul] using
      div_mul_cancel₀ (N z) hz
  have hZ0 : Z 0 = 1 := by simp [Z, tiltNumerator]
  have hDZ (k : Fin n) : coordinateDerivative Z k 0 = 0 := by
    rw [coordinateDerivative_tiltNumerator_zero_of_normExponentialDomain hD1]
    simpa using hiso.integral_coordinate k
  have hHZ : coordinateHessian Z 0 i j = if i = j then 1 else 0 := by
    rw [coordinateHessian_tiltNumerator_zero_of_normExponentialDomain hD1]
    simpa using hiso.integral_coordinate_mul i j
  have hN := coordinateHessian_tiltNumerator_zero_of_normExponentialDomain hD i j
  have hp := coordinateHessian_mul hA hZ 0 i j
  rw [heq, hZ0, hDZ, hDZ, hHZ] at hp
  have hA0 : A 0 = ∫ x, f x ∂potentialMeasure V := by simp [A]
  change coordinateHessian A 0 i j = _
  change coordinateHessian N 0 i j = _ at hN
  rw [hN, hA0] at hp
  linarith

/-- Exact degree-two coefficient, with the factorial two included. -/
theorem exponentialTiltCoordinateTaylor_two_of_isotropic
    {V f : Space n → ℝ} {κ : ℝ} [IsProbabilityMeasure (potentialMeasure V)]
    (hV : ContDiff ℝ 2 V) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian V x *ᵥ a))
    (hiso : IsIsotropic (potentialMeasure V)) (hf : MemLp f 2 (potentialMeasure V))
    (a : Fin 2 → Fin n) :
    exponentialTiltCoordinateTaylor V f 2 a =
      ((∫ x, f x * (x (a 0) * x (a 1)) ∂potentialMeasure V) -
        (∫ x, f x ∂potentialMeasure V) * (if a 0 = a 1 then 1 else 0)) / 2 := by
  have hs := contDiff_exponentialTilt_average_of_weighted_memLp hV hκ hlower hf
  have hd := ((hs.of_le (by simp) : ContDiff ℝ 2 _).fderiv_right
    (m := 1) (by norm_num)).differentiable (by norm_num) (0 : Space n)
  rw [exponentialTiltCoordinateTaylor, exponentialTiltTaylorCoefficient,
    iteratedFDeriv_two_apply, ← coordinateHessian_eq_fderiv_fderiv hd,
    coordinateHessian_exponentialTilt_average_zero_of_isotropic hV hκ hlower hiso hf]
  norm_num

end KLS
end

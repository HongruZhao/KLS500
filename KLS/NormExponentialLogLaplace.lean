import KLS.GraphExponentialMoments

/-! Actual all-order log-Laplace smoothness under all radial exponential
moments, without compact support. -/

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology BigOperators
noncomputable section
namespace KLS

lemma integrable_exp_inner_of_normExponentialDomain_one {n : ℕ}
    {μ : Measure (Space n)} (hμ : NormExponentialDomain μ (fun _ => 1)) (z : Space n) :
    Integrable (fun x => Real.exp (inner ℝ z x)) μ := by
  simpa only [one_mul] using hμ.integrable_tilt z

lemma contDiff_tiltLogLaplace_of_normExponentialDomain {n : ℕ}
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hμ : NormExponentialDomain μ (fun _ => 1)) :
    ContDiff ℝ (⊤ : ℕ∞) (tiltLogLaplace μ) := by
  have he : (fun z => tiltPartition μ (fun x => inner ℝ z x)) =
      tiltNumerator μ (fun _ => 0) (fun _ => 1) := by
    ext z
    simp only [tiltPartition, tiltNumerator, zero_add, one_mul]
  unfold tiltLogLaplace
  apply ContDiff.log
  · rw [he]
    exact contDiff_tiltNumerator_of_normExponentialDomain hμ
  · intro z
    exact (integral_exp_pos (integrable_exp_inner_of_normExponentialDomain_one hμ z)).ne'

lemma hasFDerivAt_tiltLogLaplace_of_normExponentialDomain {n : ℕ}
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hμ : NormExponentialDomain μ (fun _ => 1)) (z : Space n) :
    HasFDerivAt (tiltLogLaplace μ)
      ((tiltPartition μ (fun x => inner ℝ z x))⁻¹ •
        (∫ x, Real.exp (inner ℝ z x) • innerSL ℝ x ∂μ)) z := by
  have hd : HasFDerivAt (fun z => tiltPartition μ (fun x => inner ℝ z x))
      (∫ x, Real.exp (inner ℝ z x) • innerSL ℝ x ∂μ) z := by
    have he : (fun w => tiltPartition μ (fun x => inner ℝ w x)) =
        tiltNumerator μ (fun _ => 0) (fun _ => 1) := by
      ext w
      simp only [tiltPartition, tiltNumerator, zero_add, one_mul]
    rw [he]
    simpa only [one_mul] using
      hasFDerivAt_tiltNumerator_of_normExponentialDomain hμ z
  exact hd.log (integral_exp_pos
    (integrable_exp_inner_of_normExponentialDomain_one hμ z)).ne'

lemma fderiv_tiltLogLaplace_coordinate_of_normExponentialDomain {n : ℕ}
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hμ : NormExponentialDomain μ (fun _ => 1)) (z : Space n) (i : Fin n) :
    fderiv ℝ (tiltLogLaplace μ) z (EuclideanSpace.basisFun (Fin n) ℝ i) =
      ∫ x, x i ∂exponentialTilt μ z := by
  have hi : Integrable (fun x => Real.exp (inner ℝ z x) • innerSL ℝ x) μ := by
    simpa only [one_mul] using hμ.integrable_tilt_derivative z
  rw [(hasFDerivAt_tiltLogLaplace_of_normExponentialDomain hμ z).fderiv]
  simp only [_root_.smul_apply, smul_eq_mul]
  rw [ContinuousLinearMap.integral_apply hi]
  have he (x : Space n) :
      (Real.exp (inner ℝ z x) • innerSL ℝ x) (EuclideanSpace.basisFun (Fin n) ℝ i) =
        x i * Real.exp (inner ℝ z x) := by
    simp only [_root_.smul_apply, smul_eq_mul, innerSL_apply_apply]
    rw [real_inner_comm (EuclideanSpace.basisFun (Fin n) ℝ i) x, EuclideanSpace.basisFun_inner]
    ring
  simp_rw [he]
  change _ = tiltAverage μ (fun x => inner ℝ z x) (fun x => x i)
  rw [tiltAverage_eq_ratio]
  ring

end KLS
end
#print axioms KLS.contDiff_tiltLogLaplace_of_normExponentialDomain
#print axioms KLS.fderiv_tiltLogLaplace_coordinate_of_normExponentialDomain

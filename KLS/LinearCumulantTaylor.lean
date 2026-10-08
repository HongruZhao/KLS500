import KLS.SuspensionCumulantTaylorBound

/-! Actual Taylor coefficients of a linear observable are the actual
log-Laplace cumulant tensor with one fixed direction. -/

open MeasureTheory Set Matrix
open scoped ContDiff BigOperators ENNReal
noncomputable section
namespace KLS
set_option maxHeartbeats 1000000

lemma fderiv_tiltLogLaplace_direction_of_normExponentialDomain {n : ℕ}
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hμ : NormExponentialDomain μ (fun _ => 1)) (z u : Space n) :
    fderiv ℝ (tiltLogLaplace μ) z u = ∫ x, inner ℝ x u ∂exponentialTilt μ z := by
  have hi : Integrable (fun x => Real.exp (inner ℝ z x) • innerSL ℝ x) μ := by
    simpa only [one_mul] using hμ.integrable_tilt_derivative z
  rw [(hasFDerivAt_tiltLogLaplace_of_normExponentialDomain hμ z).fderiv]
  simp only [_root_.smul_apply, smul_eq_mul]
  rw [ContinuousLinearMap.integral_apply hi]
  change _ = tiltAverage μ (fun x => inner ℝ z x) (fun x => inner ℝ x u)
  rw [tiltAverage_eq_ratio]
  have he (x : Space n) : (Real.exp (inner ℝ z x) • innerSL ℝ x) u =
      inner ℝ x u * Real.exp (inner ℝ z x) := by
    simp only [_root_.smul_apply, smul_eq_mul, innerSL_apply_apply]
    ring
  simp_rw [he]
  ring

lemma exponentialTiltCoordinateTaylor_inner_eq_cumulant {n : ℕ} {V : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure V)]
    (hμ : NormExponentialDomain (potentialMeasure V) (fun _ => 1))
    (u : Space n) (d : ℕ) (a : Fin d → Fin n) :
    exponentialTiltCoordinateTaylor V (fun x => inner ℝ x u) d a =
      cumulantTensor (potentialMeasure V) (d + 1)
        (Fin.snoc (fun j => EuclideanSpace.basisFun (Fin n) ℝ (a j)) u) / d.factorial := by
  have he : (fun z => ∫ x, inner ℝ x u ∂exponentialTilt (potentialMeasure V) z) =
      fun z => fderiv ℝ (tiltLogLaplace (potentialMeasure V)) z u := by
    funext z
    exact (fderiv_tiltLogLaplace_direction_of_normExponentialDomain hμ z u).symm
  unfold exponentialTiltCoordinateTaylor exponentialTiltTaylorCoefficient
  rw [he]
  have hh := iteratedFDeriv_directional_comp (ContinuousLinearMap.id ℝ (Space n)) 0 u
    (((contDiff_tiltLogLaplace_of_normExponentialDomain hμ).of_le (by simp)).contDiffAt)
    (fun j => EuclideanSpace.basisFun (Fin n) ℝ (a j))
  simpa only [ContinuousLinearMap.id_apply, EuclideanSpace.basisFun_apply, cumulantTensor] using
    congrArg (fun t : ℝ => t / (d.factorial : ℝ)) hh

lemma isKLSMeasure_potential_of_coordinateHessian_lower {n : ℕ} {V : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure V)] (hV : ContDiff ℝ 2 V)
    (hμ : IsIsotropic (potentialMeasure V)) {κ : ℝ} (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian V x *ᵥ a)) :
    IsKLSMeasure (potentialMeasure V) := by
  have hc : ConvexOn ℝ univ V := convexOn_univ_of_secondFrechet_nonneg hV
    (fun x v => (mul_nonneg hκ.le (sq_nonneg _)).trans
      (secondFrechet_lower_of_coordinateHessian hV hlower x v))
  have hD : HasLogConcaveDensity (potentialMeasure V) := by
    refine ⟨(fun x => (V x : WithTop ℝ)), ?_, ?_, rfl⟩
    · simpa [ExtendedConvex] using hc.convex_epigraph
    · change Measurable (fun x => ENNReal.ofReal (Real.exp (-V x)))
      have hVm := hV.continuous.measurable
      fun_prop
  exact ⟨inferInstance, hD.absolutelyContinuousLebesgue, hD, hμ⟩

lemma Taylor_sum_le_of_universalCumulant_linear {n d : ℕ} {V : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure V)] (hV : ContDiff ℝ 2 V)
    (hμ : IsIsotropic (potentialMeasure V)) {κ b : ℝ} (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian V x *ᵥ a))
    (hglobal : UniversalDirectionalCumulantBound d b) (u : Space n) :
    (∑ a : Fin d → Fin n, exponentialTiltCoordinateTaylor V (fun x => inner ℝ x u) d a ^ 2) ≤
      (b / (d.factorial : ℝ) ^ 2) * ‖u‖ ^ 2 := by
  have hExp : NormExponentialDomain (potentialMeasure V) (fun _ => 1) :=
    normExponentialDomain_of_memLp_potentialMeasure hV hκ hlower (memLp_const (1 : ℝ))
  simp_rw [exponentialTiltCoordinateTaylor_inner_eq_cumulant hExp, div_pow]
  rw [← Finset.sum_div]
  have hh := div_le_div_of_nonneg_right
    (hglobal n _ (isKLSMeasure_potential_of_coordinateHessian_lower hV hμ hκ hlower) u)
    (sq_nonneg (d.factorial : ℝ))
  unfold directionalCumulantSquare at hh
  convert hh using 1
  ring

end KLS
end
#print axioms KLS.exponentialTiltCoordinateTaylor_inner_eq_cumulant
#print axioms KLS.Taylor_sum_le_of_universalCumulant_linear

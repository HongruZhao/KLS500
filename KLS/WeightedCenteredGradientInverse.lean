import KLS.ProbabilityMeanCentering
import KLS.WeightedOptimalInverse

/-! The actual centered gradient of the actual weighted Poisson inverse.
The range is a finite Hilbert sum of genuine L² coordinate derivatives.
The sharp bound uses the attained Rayleigh eigenvalue, whose reciprocal is
the faithful optimal Poincare constant. No classical regularity is required. -/

open MeasureTheory InnerProductSpace Matrix
open scoped ContDiff RealInnerProductSpace ENNReal

noncomputable section
namespace KLS
variable {n : ℕ}

/-- All genuine weak derivative coordinates, with the sum-of-squares L² norm. -/
def weightedH1Gradient (φ : Space n → ℝ) :
    WeightedCenteredH1 φ →L[ℝ] CenteredL2.Family (potentialMeasure φ) (Fin n) :=
  (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Fin n => Lp ℝ 2 (potentialMeasure φ))).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi (weightedH1Derivative φ))

@[simp] theorem weightedH1Gradient_apply (φ : Space n → ℝ)
    (U : WeightedCenteredH1 φ) (i : Fin n) :
    weightedH1Gradient φ U i = weightedH1Derivative φ i U := rfl

theorem weightedH1Gradient_norm_sq (φ : Space n → ℝ) (U : WeightedCenteredH1 φ) :
    ‖weightedH1Gradient φ U‖ ^ 2 = ∑ i, ‖weightedH1Derivative φ i U‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  rfl

/-- Subtract the actual mean of every genuine weak derivative. -/
def weightedH1CenteredGradient (φ : Space n → ℝ)
    [IsProbabilityMeasure (potentialMeasure φ)] :
    WeightedCenteredH1 φ →L[ℝ] CenteredL2.Family (potentialMeasure φ) (Fin n) :=
  (CenteredL2.familyCenterCLM (potentialMeasure φ) (Fin n)).comp (weightedH1Gradient φ)

@[simp] theorem weightedH1CenteredGradient_apply (φ : Space n → ℝ)
    [IsProbabilityMeasure (potentialMeasure φ)] (U : WeightedCenteredH1 φ) (i : Fin n) :
    weightedH1CenteredGradient φ U i =
      CenteredL2.center (potentialMeasure φ) (weightedH1Derivative φ i U) := by
  exact CenteredL2.familyCenterCLM_apply _ _ _

/-- Exact energy removed by subtracting the gradient's actual mean, BKL (23). -/
theorem weightedH1CenteredGradient_norm_sq (φ : Space n → ℝ)
    [IsProbabilityMeasure (potentialMeasure φ)] (U : WeightedCenteredH1 φ) :
    ‖weightedH1CenteredGradient φ U‖ ^ 2 =
      (∑ i, ‖weightedH1Derivative φ i U‖ ^ 2) -
        ∑ i, (∫ x, weightedH1Derivative φ i U x ∂potentialMeasure φ) ^ 2 := by
  change ‖CenteredL2.familyCenterCLM (potentialMeasure φ) (Fin n)
    (weightedH1Gradient φ U)‖ ^ 2 = _
  rw [CenteredL2.familyCenterCLM_norm_sq, weightedH1Gradient_norm_sq]
  rfl

theorem weightedH1CenteredGradient_norm_le (φ : Space n → ℝ)
    [IsProbabilityMeasure (potentialMeasure φ)] (U : WeightedCenteredH1 φ) :
    ‖weightedH1CenteredGradient φ U‖ ≤ ‖weightedH1Gradient φ U‖ :=
  CenteredL2.familyCenterCLM_norm_le _ _

/-- The genuine bounded linear operator `∇₀ (-Lφ)⁻¹` on weighted L². -/
def weightedCenteredGradientInverse {φ : Space n → ℝ} {κ : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a)) :
    Lp ℝ 2 (potentialMeasure φ) →L[ℝ] CenteredL2.Family (potentialMeasure φ) (Fin n) :=
  (weightedH1CenteredGradient φ).comp (weightedEnergyInverse hφ hκ hlower)

@[simp] theorem weightedCenteredGradientInverse_apply
    {φ : Space n → ℝ} {κ : ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (g : Lp ℝ 2 (potentialMeasure φ)) (i : Fin n) :
    weightedCenteredGradientInverse hφ hκ hlower g i =
      CenteredL2.center (potentialMeasure φ)
        (weightedH1Derivative φ i (weightedEnergyInverse hφ hκ hlower g)) := by
  exact weightedH1CenteredGradient_apply φ (weightedEnergyInverse hφ hκ hlower g) i

theorem weightedCenteredGradientInverse_ae {φ : Space n → ℝ} {κ : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (g : Lp ℝ 2 (potentialMeasure φ)) (i : Fin n) :
    (weightedCenteredGradientInverse hφ hκ hlower g i : Space n → ℝ)
      =ᵐ[potentialMeasure φ] fun x =>
        weightedH1Derivative φ i (weightedEnergyInverse hφ hκ hlower g) x -
          ∫ y, weightedH1Derivative φ i (weightedEnergyInverse hφ hκ hlower g) y
            ∂potentialMeasure φ := by
  rw [weightedCenteredGradientInverse_apply]
  exact CenteredL2.center_ae (potentialMeasure φ) _

theorem weightedCenteredGradientInverse_integral_eq_zero
    {φ : Space n → ℝ} {κ : ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (g : Lp ℝ 2 (potentialMeasure φ)) (i : Fin n) :
    (∫ x, weightedCenteredGradientInverse hφ hκ hlower g i x
      ∂potentialMeasure φ) = 0 := by
  simp only [weightedCenteredGradientInverse_apply]
  exact CenteredL2.integral_center (potentialMeasure φ) _

/-- The full L² inverse already removes the source's constant component. On
mean-zero data its accepted weak equation is literally `-Lφ u = g`. -/
theorem weightedEnergyInverse_center {φ : Space n → ℝ} {κ : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (g : Lp ℝ 2 (potentialMeasure φ)) :
    weightedEnergyInverse hφ hκ hlower (CenteredL2.center (potentialMeasure φ) g) =
      weightedEnergyInverse hφ hκ hlower g := by
  apply weightedEnergyInverse_unique hφ hκ hlower g
  intro V
  rw [weightedEnergyInverse_variational, CenteredL2.center, inner_sub_left,
    inner_smul_left, CenteredL2.inner_oneLp,
    weightedH1_integral_eq_zero hφ.continuous V, mul_zero, sub_zero]

theorem weightedCenteredGradientInverse_center {φ : Space n → ℝ} {κ : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (g : Lp ℝ 2 (potentialMeasure φ)) :
    weightedCenteredGradientInverse hφ hκ hlower (CenteredL2.center (potentialMeasure φ) g) =
      weightedCenteredGradientInverse hφ hκ hlower g := by
  change weightedH1CenteredGradient φ
    (weightedEnergyInverse hφ hκ hlower (CenteredL2.center (potentialMeasure φ) g)) = _
  rw [weightedEnergyInverse_center]
  rfl

/-- The actual energy bound passes through contractive mean subtraction. -/
theorem weightedCenteredGradientInverse_norm_le_of_energy
    {φ : Space n → ℝ} {κ C : ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (hC : 0 ≤ C) (g : Lp ℝ 2 (potentialMeasure φ))
    (hE : (∑ i, ‖weightedH1Derivative φ i
      (weightedEnergyInverse hφ hκ hlower g)‖ ^ 2) ≤ C * ‖g‖ ^ 2) :
    ‖weightedCenteredGradientInverse hφ hκ hlower g‖ ≤ Real.sqrt C * ‖g‖ := by
  let U := weightedEnergyInverse hφ hκ hlower g
  have hG := weightedH1CenteredGradient_norm_le φ U
  have hGs := weightedH1Gradient_norm_sq φ U
  have hsq := Real.sq_sqrt hC
  change (∑ i, ‖weightedH1Derivative φ i U‖ ^ 2) ≤ C * ‖g‖ ^ 2 at hE
  change ‖weightedH1CenteredGradient φ U‖ ≤ Real.sqrt C * ‖g‖
  have hbound : ‖weightedH1Gradient φ U‖ ≤ Real.sqrt C * ‖g‖ := by
    have heq : (Real.sqrt C * ‖g‖) ^ 2 = C * ‖g‖ ^ 2 := by
      rw [mul_pow, hsq]
    nlinarith [norm_nonneg (weightedH1Gradient φ U),
      mul_nonneg (Real.sqrt_nonneg C) (norm_nonneg g)]
  exact hG.trans hbound

/-- BKL (24) with a supplied genuine Rayleigh lower bound. -/
theorem weightedCenteredGradientInverse_norm_le_of_rayleigh
    {φ : Space n → ℝ} {κ lam : ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (hlam : 0 < lam)
    (hRay : ∀ V : WeightedCenteredH1 φ,
      lam * ‖weightedH1Value φ V‖ ^ 2 ≤ weightedEnergyForm φ V V)
    (g : Lp ℝ 2 (potentialMeasure φ)) :
    ‖weightedCenteredGradientInverse hφ hκ hlower g‖ ≤ Real.sqrt lam⁻¹ * ‖g‖ :=
  weightedCenteredGradientInverse_norm_le_of_energy hφ hκ hlower
    (inv_nonneg.mpr hlam.le) g
    (weightedEnergyInverse_energy_le_of_rayleigh hφ hκ hlower hlam hRay g)

/-- The bound is realized for an attained positive eigenvalue, whose reciprocal
is the actual optimal Poincare constant. No spectral estimate is a premise. -/
theorem exists_optimal_weightedCenteredGradientInverse_bound
    {φ : Space n → ℝ} {κ : ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
    (hn : 0 < n) (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a)) :
    ∃ lam : ℝ, 0 < lam ∧
      poincareConstant (potentialMeasure φ) = ENNReal.ofReal lam⁻¹ ∧
      ‖weightedCenteredGradientInverse hφ hκ hlower‖ ≤ Real.sqrt lam⁻¹ ∧
      ∀ g : Lp ℝ 2 (potentialMeasure φ),
        ‖weightedCenteredGradientInverse hφ hκ hlower g‖ ≤ Real.sqrt lam⁻¹ * ‖g‖ := by
  obtain ⟨lam, hlam, hCP, hbounds⟩ :=
    exists_optimal_weightedEnergyInverse_bounds hn hφ hκ hlower
  have hb (g : Lp ℝ 2 (potentialMeasure φ)) :
      ‖weightedCenteredGradientInverse hφ hκ hlower g‖ ≤ Real.sqrt lam⁻¹ * ‖g‖ :=
    weightedCenteredGradientInverse_norm_le_of_energy hφ hκ hlower
      (inv_nonneg.mpr hlam.le) g (hbounds g).2
  exact ⟨lam, hlam, hCP,
    ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) hb, hb⟩

end KLS
end

#print axioms KLS.weightedH1CenteredGradient_norm_sq
#print axioms KLS.weightedCenteredGradientInverse_ae
#print axioms KLS.weightedCenteredGradientInverse_integral_eq_zero
#print axioms KLS.weightedCenteredGradientInverse_norm_le_of_rayleigh
#print axioms KLS.exists_optimal_weightedCenteredGradientInverse_bound

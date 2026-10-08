import KLS.WeightedInverseNondegeneracy

/-! Actual finite families in the completed weighted energy graph, with genuine
value, gradient, centered gradient, and componentwise inverse maps. -/

open MeasureTheory InnerProductSpace Matrix
open scoped ContDiff RealInnerProductSpace ENNReal

noncomputable section
namespace KLS
variable {n : ℕ}

abbrev WeightedH1Family (φ : Space n → ℝ) (ι : Type*) [Fintype ι] :=
  PiLp 2 (fun _ : ι => WeightedCenteredH1 φ)

def weightedFamilyValue (φ : Space n → ℝ) (ι : Type*) [Fintype ι] :
    WeightedH1Family φ ι →L[ℝ] CenteredL2.Family (potentialMeasure φ) ι :=
  (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : ι => Lp ℝ 2 (potentialMeasure φ))).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi (fun i => (weightedH1Value φ).comp
        (PiLp.proj 2 (fun _ : ι => WeightedCenteredH1 φ) i)))

@[simp] theorem weightedFamilyValue_apply (φ : Space n → ℝ) {ι : Type*} [Fintype ι]
    (U : WeightedH1Family φ ι) (i : ι) :
    weightedFamilyValue φ ι U i = weightedH1Value φ (U i) := rfl

def weightedFamilyGradient (φ : Space n → ℝ) (ι : Type*) [Fintype ι] :
    WeightedH1Family φ ι →L[ℝ] CenteredL2.Family (potentialMeasure φ) (Fin n × ι) :=
  (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Fin n × ι => Lp ℝ 2 (potentialMeasure φ))).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi (fun ji => (weightedH1Derivative φ ji.1).comp
        (PiLp.proj 2 (fun _ : ι => WeightedCenteredH1 φ) ji.2)))

@[simp] theorem weightedFamilyGradient_apply (φ : Space n → ℝ) {ι : Type*} [Fintype ι]
    (U : WeightedH1Family φ ι) (j : Fin n) (i : ι) :
    weightedFamilyGradient φ ι U (j, i) = weightedH1Derivative φ j (U i) := rfl

theorem weightedFamilyGradient_norm_sq (φ : Space n → ℝ) {ι : Type*} [Fintype ι]
    (U : WeightedH1Family φ ι) :
    ‖weightedFamilyGradient φ ι U‖ ^ 2 = ∑ i, ∑ j : Fin n, ‖weightedH1Derivative φ j (U i)‖ ^ 2 := by
  simp only [PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type, weightedFamilyGradient_apply]
  exact Finset.sum_comm

def weightedFamilyCenteredGradient (φ : Space n → ℝ)
    [IsProbabilityMeasure (potentialMeasure φ)] (ι : Type*) [Fintype ι] :
    WeightedH1Family φ ι →L[ℝ] CenteredL2.Family (potentialMeasure φ) (Fin n × ι) :=
  (CenteredL2.familyCenterCLM (potentialMeasure φ) (Fin n × ι)).comp (weightedFamilyGradient φ ι)

@[simp] theorem weightedFamilyCenteredGradient_apply (φ : Space n → ℝ)
    [IsProbabilityMeasure (potentialMeasure φ)] {ι : Type*} [Fintype ι]
    (U : WeightedH1Family φ ι) (j : Fin n) (i : ι) :
    weightedFamilyCenteredGradient φ ι U (j, i) =
      CenteredL2.center (potentialMeasure φ) (weightedH1Derivative φ j (U i)) := by
  exact CenteredL2.familyCenterCLM_apply _ _ _

theorem weightedFamilyCenteredGradient_integral_eq_zero (φ : Space n → ℝ)
    [IsProbabilityMeasure (potentialMeasure φ)] {ι : Type*} [Fintype ι]
    (U : WeightedH1Family φ ι) (ji : Fin n × ι) :
    (∫ x, weightedFamilyCenteredGradient φ ι U ji x ∂potentialMeasure φ) = 0 := by
  rcases ji with ⟨j, i⟩
  rw [weightedFamilyCenteredGradient_apply]
  exact CenteredL2.integral_center (potentialMeasure φ) _

theorem weightedFamilyCenteredGradient_norm_sq (φ : Space n → ℝ)
    [IsProbabilityMeasure (potentialMeasure φ)] {ι : Type*} [Fintype ι]
    (U : WeightedH1Family φ ι) :
    ‖weightedFamilyCenteredGradient φ ι U‖ ^ 2 = ‖weightedFamilyGradient φ ι U‖ ^ 2 -
      ∑ ji : Fin n × ι, (∫ x, weightedFamilyGradient φ ι U ji x ∂potentialMeasure φ) ^ 2 :=
  CenteredL2.familyCenterCLM_norm_sq _ _

theorem weightedFamilyCenteredGradient_norm_le (φ : Space n → ℝ)
    [IsProbabilityMeasure (potentialMeasure φ)] {ι : Type*} [Fintype ι]
    (U : WeightedH1Family φ ι) :
    ‖weightedFamilyCenteredGradient φ ι U‖ ≤ ‖weightedFamilyGradient φ ι U‖ :=
  CenteredL2.familyCenterCLM_norm_le _ _

variable {φ : Space n → ℝ} {κ : ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))

def weightedFamilyEnergyInverse (ι : Type*) [Fintype ι] :
    CenteredL2.Family (potentialMeasure φ) ι →L[ℝ] WeightedH1Family φ ι :=
  (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : ι => WeightedCenteredH1 φ)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi (fun i => (weightedEnergyInverse hφ hκ hlower).comp
        (PiLp.proj 2 (fun _ : ι => Lp ℝ 2 (potentialMeasure φ)) i)))

@[simp] theorem weightedFamilyEnergyInverse_apply {ι : Type*} [Fintype ι]
    (g : CenteredL2.Family (potentialMeasure φ) ι) (i : ι) :
    weightedFamilyEnergyInverse hφ hκ hlower ι g i = weightedEnergyInverse hφ hκ hlower (g i) := rfl

theorem weightedFamilyEnergyInverse_gradient_eq_zero_iff {ι : Type*} [Fintype ι]
    (g : CenteredL2.Family (potentialMeasure φ) ι)
    (hg : ∀ i, (∫ x, g i x ∂potentialMeasure φ) = 0) :
    weightedFamilyGradient φ ι (weightedFamilyEnergyInverse hφ hκ hlower ι g) = 0 ↔ g = 0 := by
  constructor
  · intro hz
    apply PiLp.ext
    intro i
    change g i = 0
    apply (weightedEnergyInverse_gradient_eq_zero_iff_of_integral_eq_zero hφ hκ hlower (g i) (hg i)).mp
    apply PiLp.ext
    intro j
    have he := congrArg (fun v : CenteredL2.Family (potentialMeasure φ) (Fin n × ι) => v (j, i)) hz
    exact he
  · rintro rfl
    simp

theorem weightedFamilyEnergyInverse_gradient_norm_sq_le {ι : Type*} [Fintype ι] {C : ℝ}
    (hb : ∀ f : Lp ℝ 2 (potentialMeasure φ),
      (∑ j, ‖weightedH1Derivative φ j (weightedEnergyInverse hφ hκ hlower f)‖ ^ 2) ≤ C * ‖f‖ ^ 2)
    (g : CenteredL2.Family (potentialMeasure φ) ι) :
    ‖weightedFamilyGradient φ ι (weightedFamilyEnergyInverse hφ hκ hlower ι g)‖ ^ 2 ≤ C * ‖g‖ ^ 2 := by
  rw [weightedFamilyGradient_norm_sq, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => hb (g i))

/-- The actual variational equation summed over all tensor components. -/
theorem weightedFamilyEnergyInverse_variational {ι : Type*} [Fintype ι]
    (g : CenteredL2.Family (potentialMeasure φ) ι) (V : WeightedH1Family φ ι) :
    inner ℝ (weightedFamilyGradient φ ι (weightedFamilyEnergyInverse hφ hκ hlower ι g))
      (weightedFamilyGradient φ ι V) = inner ℝ g (weightedFamilyValue φ ι V) := by
  simp only [PiLp.inner_apply, Fintype.sum_prod_type, weightedFamilyGradient_apply,
    weightedFamilyEnergyInverse_apply, weightedFamilyValue_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← weightedEnergyForm_apply]
  exact weightedEnergyInverse_variational hφ hκ hlower (g i) (V i)

end KLS
end

#print axioms KLS.weightedFamilyEnergyInverse_gradient_eq_zero_iff
#print axioms KLS.weightedFamilyEnergyInverse_gradient_norm_sq_le
#print axioms KLS.weightedFamilyEnergyInverse_variational

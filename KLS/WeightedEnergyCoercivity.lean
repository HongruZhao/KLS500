import KLS.WeightedEnergyGraphCore
import KLS.WeightedSmoothVariance
import Mathlib.Analysis.InnerProductSpace.LaxMilgram

/-!
# Actual per-measure coercivity from a lower bound on the Hessian

The hypothesis is an explicit quadratic-form lower bound on the actual
coordinate Hessian of the potential, with an arbitrary positive constant κ.
The resulting Poincaré bound and energy coercivity are proved, not assumed.
-/

open MeasureTheory ProbabilityTheory InnerProductSpace Set Filter Matrix
open scoped ContDiff RealInnerProductSpace

noncomputable section
namespace KLS
variable {n : ℕ}

/-- An actual positive lower quadratic-form bound implies positive definiteness. -/
theorem matrix_posDef_of_positive_lower_bound {M : Matrix (Fin n) (Fin n) ℝ} {κ : ℝ}
    (hM : M.IsHermitian) (hκ : 0 < κ)
    (hlower : ∀ a : Fin n → ℝ, κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (M *ᵥ a)) : M.PosDef := by
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  refine ⟨hM, ?_⟩
  intro a ha
  have ha' : 0 < a ⬝ᵥ a := by
    simpa only [star_trivial] using (dotProduct_star_self_pos_iff.mpr ha)
  simpa only [star_trivial] using (mul_pos hκ ha').trans_le (hlower a)

/-- The inverse of an actual positive matrix obeys the reciprocal quadratic-form bound. -/
theorem matrix_inverse_quadratic_le_of_lower_bound {M : Matrix (Fin n) (Fin n) ℝ} {κ : ℝ}
    (hM : M.PosDef) (hκ : 0 < κ)
    (hlower : ∀ a : Fin n → ℝ, κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (M *ᵥ a)) (a : Fin n → ℝ) :
    a ⬝ᵥ (M⁻¹ *ᵥ a) ≤ κ⁻¹ * (a ⬝ᵥ a) := by
  let _ := hM.isUnit.invertible
  have hMa : M *ᵥ (M⁻¹ *ᵥ a) = a := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
  have hl := hlower (M⁻¹ *ᵥ a)
  rw [hMa, dotProduct_comm (M⁻¹ *ᵥ a) a] at hl
  have hs : 0 ≤ (a - κ • (M⁻¹ *ᵥ a)) ⬝ᵥ (a - κ • (M⁻¹ *ᵥ a)) := by
    simpa only [star_trivial] using dotProduct_star_self_nonneg (a - κ • (M⁻¹ *ᵥ a))
  simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul] at hs
  rw [dotProduct_comm (M⁻¹ *ᵥ a) a] at hs
  apply (le_inv_mul_iff₀ hκ).mpr
  nlinarith [mul_le_mul_of_nonneg_left hl hκ.le]

/-- The lower bound on the actual Hessian controls its inverse-gradient form pointwise. -/
theorem inverseHessianGradientForm_le_of_hessian_lower_bound {φ f : Space n → ℝ} {κ : ℝ}
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a)) (x : Space n) :
    inverseHessianGradientForm φ f x ≤
      κ⁻¹ * ∑ i : Fin n, (coordinateDerivative f i x) ^ 2 := by
  have hp := matrix_posDef_of_positive_lower_bound
    (Matrix.isHermitian_iff_isSymm.mpr (coordinateHessian_symmetric hφ x)) hκ (hlower x)
  rw [inverseHessianGradientForm, matrix_quadratic_sum_eq_dotProduct]
  simpa only [dotProduct, pow_two] using
    matrix_inverse_quadratic_le_of_lower_bound hp hκ (hlower x)
      (fun i => coordinateDerivative f i x)


/-- Smooth compact tests satisfy the per-measure Poincaré bound derived from the actual Hessian. -/
theorem variance_le_gradient_energy_of_hessian_lower_bound {φ f : Space n → ℝ} {κ : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a)) :
    ProbabilityTheory.variance f (potentialMeasure φ) ≤
      κ⁻¹ * ∑ i : Fin n, ∫ x, (coordinateDerivative f i x) ^ 2 ∂potentialMeasure φ := by
  have hpos (x : Space n) : (coordinateHessian φ x).PosDef :=
    matrix_posDef_of_positive_lower_bound
      (Matrix.isHermitian_iff_isSymm.mpr (coordinateHessian_symmetric hφ x)) hκ (hlower x)
  have hd2 (i : Fin n) : MemLp (coordinateDerivative f i) 2 (potentialMeasure φ) :=
    memLp_of_continuous_hasCompactSupport hφ.continuous
      (contDiff_coordinateDerivative hf (m := 0) (by norm_num) i).continuous
      (hasCompactSupport_coordinateDerivative hc i)
  have hsum := integrable_finsetSum Finset.univ (fun i _ => (hd2 i).integrable_sq)
  have hcomp := integral_mono (integrable_inverseHessianGradientForm hφ hf hpos hc)
    (hsum.const_mul κ⁻¹)
    (inverseHessianGradientForm_le_of_hessian_lower_bound hφ hκ hlower)
  rw [integral_const_mul, integral_finsetSum Finset.univ (fun i _ => (hd2 i).integrable_sq)] at hcomp
  exact (brascampLieb_variance_smooth_compact hφ hf hpos hc).trans hcomp

/-- The Poincaré bound holds on the actual smooth centered-gradient core. -/
theorem smoothCenteredGradientGraphSet_value_norm_sq_le {φ : Space n → ℝ} {κ : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    {U : WeightedEnergyAmbient φ} (hU : U ∈ smoothCenteredGradientGraphSet φ) :
    ‖U 0‖ ^ 2 ≤ κ⁻¹ * ∑ i : Fin n, ‖U i.succ‖ ^ 2 := by
  obtain ⟨f, hf, hc, hv, hd⟩ := hU
  have hvnorm : ‖U 0‖ ^ 2 = ProbabilityTheory.variance f (potentialMeasure φ) := by
    rw [ProbabilityTheory.variance_eq_integral hf.continuous.aemeasurable,
      ← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hv] with x hx
    simp [hx, pow_two]
  have hdnorm (i : Fin n) : ‖U i.succ‖ ^ 2 =
      ∫ x, (coordinateDerivative f i x) ^ 2 ∂potentialMeasure φ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hd i] with x hx
    simp [hx, pow_two]
  rw [hvnorm]
  simp_rw [hdnorm]
  exact variance_le_gradient_energy_of_hessian_lower_bound hφ (hf.of_le (by norm_num)) hc hκ hlower

/-- The actual lower-Hessian bound proves Poincaré on every element of the completed graph. -/
theorem weightedH1_value_norm_sq_le_energy {φ : Space n → ℝ} {κ : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (U : WeightedCenteredH1 φ) :
    ‖weightedH1Value φ U‖ ^ 2 ≤ κ⁻¹ * ∑ i : Fin n, ‖weightedH1Derivative φ i U‖ ^ 2 := by
  have hclosed : IsClosed {W : WeightedEnergyAmbient φ |
      ‖W 0‖ ^ 2 ≤ κ⁻¹ * ∑ i : Fin n, ‖W i.succ‖ ^ 2} :=
    isClosed_le (by fun_prop) (by fun_prop)
  have hcore : smoothCenteredGradientGraphSet φ ⊆ {W : WeightedEnergyAmbient φ |
      ‖W 0‖ ^ 2 ≤ κ⁻¹ * ∑ i : Fin n, ‖W i.succ‖ ^ 2} :=
    fun _ hW => smoothCenteredGradientGraphSet_value_norm_sq_le hφ hκ hlower hW
  have hU : (U : WeightedEnergyAmbient φ) ∈ closure (smoothCenteredGradientGraphSet φ) := by
    rw [← weightedCenteredGradientGraph_coe_eq_closure hφ.continuous]
    exact U.property
  exact (closure_minimal hcore hclosed) hU

/-- The genuine continuous Dirichlet bilinear form on the complete weighted energy graph. -/
def weightedEnergyForm (φ : Space n → ℝ) :
    WeightedCenteredH1 φ →L[ℝ] WeightedCenteredH1 φ →L[ℝ] ℝ :=
  ∑ i : Fin n, (innerSL ℝ).bilinearComp
    (weightedH1Derivative φ i) (weightedH1Derivative φ i)

@[simp] theorem weightedEnergyForm_apply (φ : Space n → ℝ) (U V : WeightedCenteredH1 φ) :
    weightedEnergyForm φ U V =
      ∑ i : Fin n, inner ℝ (weightedH1Derivative φ i U) (weightedH1Derivative φ i V) := by
  simp [weightedEnergyForm]

@[simp] theorem weightedEnergyForm_self (φ : Space n → ℝ) (U : WeightedCenteredH1 φ) :
    weightedEnergyForm φ U U = ∑ i : Fin n, ‖weightedH1Derivative φ i U‖ ^ 2 := by
  simp [weightedEnergyForm_apply]

/-- The continuous form is the sum of integrals of the actual weak derivative coordinates. -/
theorem weightedEnergyForm_eq_sum_integral (φ : Space n → ℝ) (U V : WeightedCenteredH1 φ) :
    weightedEnergyForm φ U V = ∑ i : Fin n,
      ∫ x, weightedH1Derivative φ i U x * weightedH1Derivative φ i V x ∂potentialMeasure φ := by
  rw [weightedEnergyForm_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [L2.inner_def]
  apply integral_congr_ae
  exact Eventually.of_forall fun _ => by simp [RCLike.inner_apply, mul_comm]

/-- The Dirichlet form is symmetric because it uses the actual L² inner products. -/
theorem weightedEnergyForm_symm (φ : Space n → ℝ) (U V : WeightedCenteredH1 φ) :
    weightedEnergyForm φ U V = weightedEnergyForm φ V U := by
  simp only [weightedEnergyForm_apply]
  exact Finset.sum_congr rfl (fun _ _ => real_inner_comm _ _)

/-- A positive lower bound on the actual Hessian makes the energy form coercive.
The explicit constant `(1 + κ⁻¹)⁻¹` can depend on this measure through κ. -/
theorem weightedEnergyForm_isCoercive {φ : Space n → ℝ} {κ : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a)) :
    IsCoercive (weightedEnergyForm φ) := by
  have hp : 0 < 1 + κ⁻¹ := by positivity
  refine ⟨(1 + κ⁻¹)⁻¹, inv_pos.mpr hp, ?_⟩
  intro U
  have hP := weightedH1_value_norm_sq_le_energy hφ hκ hlower U
  have hn := weightedH1_norm_sq φ U
  rw [weightedEnergyForm_self]
  calc
    (1 + κ⁻¹)⁻¹ * ‖U‖ * ‖U‖ = (1 + κ⁻¹)⁻¹ * ‖U‖ ^ 2 := by ring
    _ ≤ ∑ i : Fin n, ‖weightedH1Derivative φ i U‖ ^ 2 :=
      (inv_mul_le_iff₀ hp).mpr (by nlinarith)

end KLS
end

#print axioms KLS.matrix_posDef_of_positive_lower_bound
#print axioms KLS.matrix_inverse_quadratic_le_of_lower_bound
#print axioms KLS.inverseHessianGradientForm_le_of_hessian_lower_bound

#print axioms KLS.variance_le_gradient_energy_of_hessian_lower_bound
#print axioms KLS.weightedH1_value_norm_sq_le_energy
#print axioms KLS.weightedEnergyForm_isCoercive

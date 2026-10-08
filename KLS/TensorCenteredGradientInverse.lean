import KLS.WeightedCenteredGradientInverse

/-! Componentwise extension of the actual centered Poisson gradient to every
finite tensor family, with the Hilbert-Schmidt L² norm. A derivative index is
placed first. The scalar attained-eigenvalue bound is retained unchanged. -/

open MeasureTheory InnerProductSpace Matrix
open scoped ContDiff RealInnerProductSpace ENNReal

noncomputable section
namespace KLS

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Apply an actual finite-vector L² operator to every component; its new index
is first, as in the tensor-gradient convention. -/
def finiteL2VectorLift {J : Type*} [Fintype J]
    (T : Lp ℝ 2 μ →L[ℝ] CenteredL2.Family μ J)
    (ι : Type*) [Fintype ι] :
    CenteredL2.Family μ ι →L[ℝ] CenteredL2.Family μ (J × ι) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : J × ι => Lp ℝ 2 μ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun ji =>
      ((PiLp.proj 2 (fun _ : J => Lp ℝ 2 μ) ji.1).comp T).comp
        (PiLp.proj 2 (fun _ : ι => Lp ℝ 2 μ) ji.2)))

@[simp] theorem finiteL2VectorLift_apply {J ι : Type*} [Fintype J] [Fintype ι]
    (T : Lp ℝ 2 μ →L[ℝ] CenteredL2.Family μ J)
    (g : CenteredL2.Family μ ι) (j : J) (i : ι) :
    finiteL2VectorLift T ι g (j, i) = T (g i) j := rfl

theorem finiteL2VectorLift_norm_sq {J ι : Type*} [Fintype J] [Fintype ι]
    (T : Lp ℝ 2 μ →L[ℝ] CenteredL2.Family μ J) (g : CenteredL2.Family μ ι) :
    ‖finiteL2VectorLift T ι g‖ ^ 2 = ∑ i, ‖T (g i)‖ ^ 2 := by
  simp only [PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type, finiteL2VectorLift_apply]
  exact Finset.sum_comm

/-- Finite componentwise extension does not enlarge a Hilbert L² operator bound. -/
theorem finiteL2VectorLift_norm_le {J ι : Type*} [Fintype J] [Fintype ι]
    (T : Lp ℝ 2 μ →L[ℝ] CenteredL2.Family μ J) {C : ℝ}
    (hC : 0 ≤ C) (hT : ∀ f, ‖T f‖ ≤ C * ‖f‖) (g : CenteredL2.Family μ ι) :
    ‖finiteL2VectorLift T ι g‖ ≤ C * ‖g‖ := by
  have hs : ∑ i, ‖T (g i)‖ ^ 2 ≤ ∑ i, (C * ‖g i‖) ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mpr (hT (g i))
  have he : (∑ i, (C * ‖g i‖) ^ 2) = (C * ‖g‖) ^ 2 := by
    simp only [mul_pow, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  rw [← finiteL2VectorLift_norm_sq T g, he] at hs
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp hs

theorem finiteL2VectorLift_opNorm_le {J : Type*} [Fintype J]
    (T : Lp ℝ 2 μ →L[ℝ] CenteredL2.Family μ J) (ι : Type*) [Fintype ι] :
    ‖finiteL2VectorLift T ι‖ ≤ ‖T‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
    (finiteL2VectorLift_norm_le T (norm_nonneg T) T.le_opNorm)

variable {n : ℕ}

/-- The actual tensor-valued centered Poisson gradient, componentwise. -/
def weightedTensorCenteredGradientInverse {φ : Space n → ℝ} {κ : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (ι : Type*) [Fintype ι] :
    CenteredL2.Family (potentialMeasure φ) ι →L[ℝ]
      CenteredL2.Family (potentialMeasure φ) (Fin n × ι) :=
  finiteL2VectorLift (weightedCenteredGradientInverse hφ hκ hlower) ι

/-- Exact tensor energy identity: the sum of derivative energies minus the
sum of squares of the actual componentwise derivative means. -/
theorem weightedTensorCenteredGradientInverse_norm_sq
    {φ : Space n → ℝ} {κ : ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    {ι : Type*} [Fintype ι] (g : CenteredL2.Family (potentialMeasure φ) ι) :
    ‖weightedTensorCenteredGradientInverse hφ hκ hlower ι g‖ ^ 2 =
      (∑ i, ∑ j : Fin n, ‖weightedH1Derivative φ j
        (weightedEnergyInverse hφ hκ hlower (g i))‖ ^ 2) -
      ∑ i, ∑ j : Fin n, (∫ x, weightedH1Derivative φ j
        (weightedEnergyInverse hφ hκ hlower (g i)) x ∂potentialMeasure φ) ^ 2 := by
  rw [weightedTensorCenteredGradientInverse, finiteL2VectorLift_norm_sq]
  simp only [weightedCenteredGradientInverse, ContinuousLinearMap.comp_apply,
    weightedH1CenteredGradient_norm_sq]
  rw [Finset.sum_sub_distrib]

theorem weightedTensorCenteredGradientInverse_ae
    {φ : Space n → ℝ} {κ : ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    {ι : Type*} [Fintype ι] (g : CenteredL2.Family (potentialMeasure φ) ι)
    (j : Fin n) (i : ι) :
    (weightedTensorCenteredGradientInverse hφ hκ hlower ι g (j, i) : Space n → ℝ)
      =ᵐ[potentialMeasure φ] fun x =>
        weightedH1Derivative φ j (weightedEnergyInverse hφ hκ hlower (g i)) x -
          ∫ y, weightedH1Derivative φ j (weightedEnergyInverse hφ hκ hlower (g i)) y
            ∂potentialMeasure φ :=
  weightedCenteredGradientInverse_ae hφ hκ hlower (g i) j

theorem weightedTensorCenteredGradientInverse_integral_eq_zero
    {φ : Space n → ℝ} {κ : ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    {ι : Type*} [Fintype ι] (g : CenteredL2.Family (potentialMeasure φ) ι)
    (j : Fin n) (i : ι) :
    (∫ x, weightedTensorCenteredGradientInverse hφ hκ hlower ι g (j, i) x
      ∂potentialMeasure φ) = 0 :=
  weightedCenteredGradientInverse_integral_eq_zero hφ hκ hlower (g i) j

/-- A single attained eigenvalue controls all finite tensor ranks. The actual
Poincare constant identifies this eigenvalue; no universal gap is asserted. -/
theorem exists_optimal_weightedTensorCenteredGradientInverse_bound
    {φ : Space n → ℝ} {κ : ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
    (hn : 0 < n) (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a)) :
    ∃ lam : ℝ, 0 < lam ∧
      poincareConstant (potentialMeasure φ) = ENNReal.ofReal lam⁻¹ ∧
      ∀ (ι : Type*) [Fintype ι],
        ‖weightedTensorCenteredGradientInverse hφ hκ hlower ι‖ ≤ Real.sqrt lam⁻¹ ∧
        ∀ g : CenteredL2.Family (potentialMeasure φ) ι,
          ‖weightedTensorCenteredGradientInverse hφ hκ hlower ι g‖ ≤
            Real.sqrt lam⁻¹ * ‖g‖ := by
  obtain ⟨lam, hlam, hCP, hop, hb⟩ :=
    exists_optimal_weightedCenteredGradientInverse_bound hn hφ hκ hlower
  refine ⟨lam, hlam, hCP, fun ι _ => ⟨?_, ?_⟩⟩
  · exact (finiteL2VectorLift_opNorm_le
      (weightedCenteredGradientInverse hφ hκ hlower) ι).trans hop
  · exact finiteL2VectorLift_norm_le _ (Real.sqrt_nonneg _) hb

end KLS
end

#print axioms KLS.finiteL2VectorLift_norm_sq
#print axioms KLS.finiteL2VectorLift_opNorm_le
#print axioms KLS.weightedTensorCenteredGradientInverse_ae
#print axioms KLS.exists_optimal_weightedTensorCenteredGradientInverse_bound

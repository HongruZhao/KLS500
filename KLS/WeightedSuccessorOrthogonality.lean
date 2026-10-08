import KLS.WeightedNormalizedSuccessor

/-! Genuine one-step orthogonality from the variational inverse equation. The
test family consists of actual energy-graph representatives of the centered
derivatives. A later smooth-domain theorem constructs these representatives. -/

open MeasureTheory InnerProductSpace Matrix
open scoped ContDiff RealInnerProductSpace ENNReal

noncomputable section
namespace KLS
variable {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))

def weightedSuccessorForcing {ι : Type*} [Fintype ι] (U : WeightedH1Family φ ι) :
    CenteredL2.Family (potentialMeasure φ) (Fin n × ι) :=
  weightedSuccessorScale hφ hκ hlower U • weightedFamilyCenteredGradient φ ι U

def weightedSuccessorHessianDefect {ι : Type*} [Fintype ι]
    (U : WeightedH1Family φ ι) (W : WeightedH1Family φ (Fin n × ι)) : ℝ :=
  ‖weightedFamilyGradient φ (Fin n × ι) W -
    weightedSuccessorScale hφ hκ hlower U • weightedFamilyGradient φ (Fin n × ι)
      (weightedNormalizedSuccessor hφ hκ hlower U)‖ ^ 2

/-- Test the genuine successor equation against the actual centered derivatives. -/
theorem weightedSuccessor_hessian_pairing {ι : Type*} [Fintype ι]
    (U : WeightedH1Family φ ι) (W : WeightedH1Family φ (Fin n × ι))
    (hW : weightedFamilyValue φ (Fin n × ι) W = weightedFamilyCenteredGradient φ ι U) :
    inner ℝ (weightedFamilyGradient φ (Fin n × ι) W)
      (weightedFamilyGradient φ (Fin n × ι) (weightedNormalizedSuccessor hφ hκ hlower U)) =
      weightedSuccessorScale hφ hκ hlower U *
        ‖weightedFamilyGradient φ (Fin n × ι) (weightedNormalizedSuccessor hφ hκ hlower U)‖ ^ 2 := by
  rw [weightedNormalizedSuccessor_gradient_norm]
  rw [weightedNormalizedSuccessor, map_smul, inner_smul_right, real_inner_comm]
  rw [weightedFamilyEnergyInverse_variational, hW, real_inner_self_eq_norm_sq]

/-- The defect is orthogonal to the actual successor gradient, including the zero branch. -/
theorem weightedSuccessor_hessian_orthogonal {ι : Type*} [Fintype ι]
    (U : WeightedH1Family φ ι) (W : WeightedH1Family φ (Fin n × ι))
    (hW : weightedFamilyValue φ (Fin n × ι) W = weightedFamilyCenteredGradient φ ι U) :
    inner ℝ (weightedFamilyGradient φ (Fin n × ι) W -
      weightedSuccessorScale hφ hκ hlower U • weightedFamilyGradient φ (Fin n × ι)
        (weightedNormalizedSuccessor hφ hκ hlower U))
      (weightedFamilyGradient φ (Fin n × ι) (weightedNormalizedSuccessor hφ hκ hlower U)) = 0 := by
  rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
    weightedSuccessor_hessian_pairing hφ hκ hlower U W hW, sub_self]

/-- Pythagoras for the actual Hessian and successor gradient, BKL (39). -/
theorem weightedSuccessor_hessian_energy_identity {ι : Type*} [Fintype ι]
    (U : WeightedH1Family φ ι) (W : WeightedH1Family φ (Fin n × ι))
    (hW : weightedFamilyValue φ (Fin n × ι) W = weightedFamilyCenteredGradient φ ι U) :
    ‖weightedFamilyGradient φ (Fin n × ι) W‖ ^ 2 =
      (weightedSuccessorScale hφ hκ hlower U) ^ 2 *
        ‖weightedFamilyGradient φ (Fin n × ι) (weightedNormalizedSuccessor hφ hκ hlower U)‖ ^ 2 +
          weightedSuccessorHessianDefect hφ hκ hlower U W := by
  have hp := weightedSuccessor_hessian_pairing hφ hκ hlower U W hW
  unfold weightedSuccessorHessianDefect
  rw [norm_sub_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [hp]
  ring

theorem weightedSuccessorForcing_norm_sq {ι : Type*} [Fintype ι]
    (U : WeightedH1Family φ ι) :
    ‖weightedSuccessorForcing hφ hκ hlower U‖ ^ 2 =
      (weightedSuccessorScale hφ hκ hlower U) ^ 2 *
        ‖weightedFamilyGradient φ (Fin n × ι) (weightedNormalizedSuccessor hφ hκ hlower U)‖ ^ 2 := by
  rw [weightedSuccessorForcing, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    weightedNormalizedSuccessor_gradient_norm]

/-- The full Hessian energy is the next forcing energy plus the orthogonal defect. -/
theorem weightedSuccessor_hessian_energy_eq_forcing_add_defect {ι : Type*} [Fintype ι]
    (U : WeightedH1Family φ ι) (W : WeightedH1Family φ (Fin n × ι))
    (hW : weightedFamilyValue φ (Fin n × ι) W = weightedFamilyCenteredGradient φ ι U) :
    ‖weightedFamilyGradient φ (Fin n × ι) W‖ ^ 2 =
      ‖weightedSuccessorForcing hφ hκ hlower U‖ ^ 2 +
        weightedSuccessorHessianDefect hφ hκ hlower U W := by
  rw [weightedSuccessorForcing_norm_sq]
  exact weightedSuccessor_hessian_energy_identity hφ hκ hlower U W hW

/-- Centering and scaling the true Hessian controls the next centered gradient
by the actual orthogonal defect. -/
theorem weightedSuccessor_centered_hessian_approximation {ι : Type*} [Fintype ι]
    (U : WeightedH1Family φ ι) (W : WeightedH1Family φ (Fin n × ι))
    {lam : ℝ} (hlam : 0 < lam)
    (ha : 0 < weightedSuccessorScale hφ hκ hlower U)
    (hla : lam ≤ (weightedSuccessorScale hφ hκ hlower U) ^ 2) :
    ‖weightedFamilyCenteredGradient φ (Fin n × ι) (weightedNormalizedSuccessor hφ hκ hlower U) -
      (weightedSuccessorScale hφ hκ hlower U)⁻¹ • weightedFamilyCenteredGradient φ (Fin n × ι) W‖ ^ 2 ≤
        weightedSuccessorHessianDefect hφ hκ hlower U W / lam := by
  let a := weightedSuccessorScale hφ hκ hlower U
  let H := weightedFamilyGradient φ (Fin n × ι) W
  let V := weightedFamilyGradient φ (Fin n × ι) (weightedNormalizedSuccessor hφ hκ hlower U)
  let P := CenteredL2.familyCenterCLM (potentialMeasure φ) (Fin n × (Fin n × ι))
  have ha' : 0 < a := ha
  have he : P V - a⁻¹ • P H = (-a⁻¹) • P (H - a • V) := by
    rw [map_sub, map_smul, smul_sub, smul_smul]
    have hh : -a⁻¹ * a = -1 := by rw [neg_mul, inv_mul_cancel₀ ha'.ne']
    rw [hh]
    module
  have hn : ‖P V - a⁻¹ • P H‖ ≤ a⁻¹ * ‖H - a • V‖ := by
    rw [he, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg (inv_nonneg.mpr ha'.le)]
    exact mul_le_mul_of_nonneg_left (CenteredL2.familyCenterCLM_norm_le _ _)
      (inv_nonneg.mpr ha'.le)
  have hs : ‖P V - a⁻¹ • P H‖ ^ 2 ≤ (a⁻¹ * ‖H - a • V‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (inv_nonneg.mpr ha'.le) (norm_nonneg _))).mpr hn
  have hinv : (a ^ 2)⁻¹ ≤ lam⁻¹ := (inv_le_inv₀ (sq_pos_of_pos ha') hlam).mpr hla
  change ‖P V - a⁻¹ • P H‖ ^ 2 ≤ ‖H - a • V‖ ^ 2 / lam
  calc
    _ ≤ (a⁻¹) ^ 2 * ‖H - a • V‖ ^ 2 := by simpa only [mul_pow] using hs
    _ ≤ lam⁻¹ * ‖H - a • V‖ ^ 2 := by
      rw [inv_pow]
      exact mul_le_mul_of_nonneg_right hinv (sq_nonneg _)
    _ = _ := by ring

end KLS
end

#print axioms KLS.weightedSuccessor_hessian_orthogonal
#print axioms KLS.weightedSuccessor_hessian_energy_identity
#print axioms KLS.weightedSuccessor_hessian_energy_eq_forcing_add_defect
#print axioms KLS.weightedSuccessor_centered_hessian_approximation

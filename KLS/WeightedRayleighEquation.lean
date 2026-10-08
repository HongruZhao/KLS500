import KLS.WeightedRayleighMinimizer
import Mathlib.Algebra.QuadraticDiscriminant

/-! The attained actual Rayleigh minimum satisfies the weak energy eigenvalue equation. -/
open MeasureTheory InnerProductSpace Set Filter Matrix
open scoped ContDiff RealInnerProductSpace
noncomputable section
namespace KLS
variable {n : ℕ}

/-- Homogeneous normalization converts the unit-value minimum into the full Rayleigh lower bound. -/
theorem weightedRayleigh_minimizer_lower_bound {φ : Space n → ℝ}
    {U : WeightedCenteredH1 φ}
    (hmin : ∀ V : WeightedCenteredH1 φ, ‖weightedH1Value φ V‖ = 1 →
      weightedEnergyForm φ U U ≤ weightedEnergyForm φ V V)
    (V : WeightedCenteredH1 φ) :
    weightedEnergyForm φ U U * ‖weightedH1Value φ V‖ ^ 2 ≤ weightedEnergyForm φ V V := by
  by_cases hV : weightedH1Value φ V = 0
  · simp only [hV, norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero, weightedEnergyForm_self]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  · let c : ℝ := ‖weightedH1Value φ V‖⁻¹
    let W : WeightedCenteredH1 φ := c • V
    have hr : ‖weightedH1Value φ V‖ ≠ 0 := norm_ne_zero_iff.mpr hV
    have hW : ‖weightedH1Value φ W‖ = 1 := by
      dsimp only [W, c]
      rw [map_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
        inv_mul_cancel₀ hr]
    have hb := hmin W hW
    have he : ‖weightedH1Value φ V‖ ^ 2 * weightedEnergyForm φ W W =
        weightedEnergyForm φ V V := by
      dsimp only [W, c]
      simp only [map_smul, _root_.smul_apply, smul_eq_mul]
      field_simp [hr]
    have hh := mul_le_mul_of_nonneg_left hb (sq_nonneg ‖weightedH1Value φ V‖)
    nlinarith

private lemma weightedEnergyForm_add_smul_self (φ : Space n → ℝ)
    (U V : WeightedCenteredH1 φ) (t : ℝ) :
    weightedEnergyForm φ (U + t • V) (U + t • V) =
      weightedEnergyForm φ U U + 2 * t * weightedEnergyForm φ U V +
        t ^ 2 * weightedEnergyForm φ V V := by
  simp only [map_add, map_smul, _root_.add_apply, _root_.smul_apply,
    smul_eq_mul]
  rw [weightedEnergyForm_symm φ V U]
  ring

/-- The actual minimizer obeys the weak energy equation on the entire completed graph. -/
theorem weightedRayleigh_minimizer_variational {φ : Space n → ℝ}
    {U : WeightedCenteredH1 φ} (hU : ‖weightedH1Value φ U‖ = 1)
    (hmin : ∀ V : WeightedCenteredH1 φ, ‖weightedH1Value φ V‖ = 1 →
      weightedEnergyForm φ U U ≤ weightedEnergyForm φ V V)
    (V : WeightedCenteredH1 φ) :
    weightedEnergyForm φ U V = weightedEnergyForm φ U U *
      inner ℝ (weightedH1Value φ U) (weightedH1Value φ V) := by
  have hpoly (t : ℝ) :
      0 ≤ (weightedEnergyForm φ V V - weightedEnergyForm φ U U * ‖weightedH1Value φ V‖ ^ 2) *
          (t * t) +
        (2 * (weightedEnergyForm φ U V - weightedEnergyForm φ U U *
          inner ℝ (weightedH1Value φ U) (weightedH1Value φ V))) * t + 0 := by
    have h := weightedRayleigh_minimizer_lower_bound hmin (U + t • V)
    have hv : ‖weightedH1Value φ (U + t • V)‖ ^ 2 =
        1 + 2 * t * inner ℝ (weightedH1Value φ U) (weightedH1Value φ V) +
          t ^ 2 * ‖weightedH1Value φ V‖ ^ 2 := by
      rw [map_add, map_smul, norm_add_sq_real, hU]
      simp only [one_pow, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      ring
    rw [weightedEnergyForm_add_smul_self, hv] at h
    nlinarith
  have hd := discrim_le_zero hpoly
  dsimp only [discrim] at hd
  nlinarith [sq_nonneg (weightedEnergyForm φ U V - weightedEnergyForm φ U U *
    inner ℝ (weightedH1Value φ U) (weightedH1Value φ V))]

/-- A positive actual first weak eigenpair exists for each normalized confined potential.
This is a graph-space variational equation and makes no classical regularity claim. -/
theorem exists_positive_weighted_weak_eigenpair {φ : Space n → ℝ} {κ : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hn : 0 < n) (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a)) :
    ∃ (lam : ℝ) (U : WeightedCenteredH1 φ), κ ≤ lam ∧ 0 < lam ∧
      ‖weightedH1Value φ U‖ = 1 ∧
      (∀ V : WeightedCenteredH1 φ,
        weightedEnergyForm φ U V = lam * inner ℝ (weightedH1Value φ U) (weightedH1Value φ V)) ∧
      (∀ V : WeightedCenteredH1 φ, ‖weightedH1Value φ V‖ = 1 →
        lam ≤ weightedEnergyForm φ V V) := by
  obtain ⟨lam, U, hκlam, hlam, hU, he, hmin⟩ :=
    exists_positive_weightedRayleigh_minimizer hn hφ hκ hlower
  have henergy : lam = weightedEnergyForm φ U U := by simpa only [weightedEnergyForm_self] using he
  have hmin' : ∀ V : WeightedCenteredH1 φ, ‖weightedH1Value φ V‖ = 1 →
      weightedEnergyForm φ U U ≤ weightedEnergyForm φ V V := by
    intro V hV
    rw [← henergy, weightedEnergyForm_self]
    exact hmin V hV
  refine ⟨lam, U, hκlam, hlam, hU, ?_, ?_⟩
  · intro V
    rw [henergy]
    exact weightedRayleigh_minimizer_variational hU hmin' V
  · intro V hV
    simpa only [weightedEnergyForm_self] using hmin V hV

end KLS
end
#print axioms KLS.weightedRayleigh_minimizer_lower_bound
#print axioms KLS.weightedRayleigh_minimizer_variational
#print axioms KLS.exists_positive_weighted_weak_eigenpair

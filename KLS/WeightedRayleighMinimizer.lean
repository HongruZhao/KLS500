import KLS.WeightedGlobalCompactEmbedding
import KLS.WeightedEnergyNontrivial
import EllipticPdes.Analysis.DirectMethodForm

/-! Actual attainment of the first weighted Rayleigh quotient for each confined potential. -/
open MeasureTheory InnerProductSpace Set Filter Matrix
open scoped ContDiff RealInnerProductSpace
noncomputable section
namespace KLS
variable {n : ℕ}

/-- Actual per-measure Rayleigh attainment on the genuine completed centered gradient graph.
Compactness, coercivity, and nonemptiness are proved from the displayed hypotheses. -/
theorem exists_weightedRayleigh_minimizer {φ : Space n → ℝ} {κ : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hn : 0 < n) (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a)) :
    ∃ U : WeightedCenteredH1 φ, ‖weightedH1Value φ U‖ = 1 ∧
      ∀ V : WeightedCenteredH1 φ, ‖weightedH1Value φ V‖ = 1 →
        (∑ i : Fin n, ‖weightedH1Derivative φ i U‖ ^ 2) ≤
          ∑ i : Fin n, ‖weightedH1Derivative φ i V‖ ^ 2 := by
  obtain ⟨U, hU, hmin⟩ := EllipticPdes.Analysis.exists_bilin_minimiser
    (weightedEnergyForm_isCoercive hφ hκ hlower) (weightedEnergyForm_symm φ)
    (weightedH1Value φ) (weightedH1Value_isCompactOperator hφ hκ hlower)
    (exists_weightedH1_value_norm_eq_one hn hφ.continuous)
  refine ⟨U, hU, ?_⟩
  intro V hV
  simpa only [weightedEnergyForm_self] using hmin V hV

/-- The attained first Rayleigh value is positive, with the derived lower bound κ. -/
theorem exists_positive_weightedRayleigh_minimizer {φ : Space n → ℝ} {κ : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hn : 0 < n) (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a)) :
    ∃ (lam : ℝ) (U : WeightedCenteredH1 φ), κ ≤ lam ∧ 0 < lam ∧
      ‖weightedH1Value φ U‖ = 1 ∧
      lam = ∑ i : Fin n, ‖weightedH1Derivative φ i U‖ ^ 2 ∧
      ∀ V : WeightedCenteredH1 φ, ‖weightedH1Value φ V‖ = 1 →
        lam ≤ ∑ i : Fin n, ‖weightedH1Derivative φ i V‖ ^ 2 := by
  obtain ⟨U, hU, hmin⟩ := exists_weightedRayleigh_minimizer hn hφ hκ hlower
  let lam : ℝ := ∑ i : Fin n, ‖weightedH1Derivative φ i U‖ ^ 2
  have hP := weightedH1_value_norm_sq_le_energy hφ hκ hlower U
  rw [hU, one_pow] at hP
  have hlam : κ ≤ lam := by
    have h := mul_le_mul_of_nonneg_left hP hκ.le
    rwa [mul_one, ← mul_assoc, mul_inv_cancel₀ hκ.ne', one_mul] at h
  exact ⟨lam, U, hlam, hκ.trans_le hlam, hU, rfl, hmin⟩

end KLS
end
#print axioms KLS.exists_weightedRayleigh_minimizer
#print axioms KLS.exists_positive_weightedRayleigh_minimizer

import SpectralReductionRankSumRecurrence
import KLS.WeightedIterationMeanLossBound
import KLS.WeightedEigenIterationSymmetrization
import SpectralReductionRankScalar
import SpectralReductionRankSymmetrization
import KLS.ThirdCumulant

/-! Reduced regular spectral criterion for the same faithful Poincare constant.
The scalar coordinate-Taylor norm bound remains an explicit premise. All
iteration, eigenvalue, defect, stopping, and mean-loss inputs are derived. -/

open MeasureTheory InnerProductSpace Matrix
open scoped ContDiff RealInnerProductSpace Topology BigOperators
noncomputable section
namespace KLS.ConstantReduction
variable {n : ℕ}

/-- An actual coordinate-Taylor bound controls the faithful optimal
Poincare constant of a smooth uniformly convex probability potential. -/
theorem poincareConstant_le_of_rankTaylorBound_twentyNine
    {φ : Space n → ℝ} {κ : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hn : 0 < n) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (hsecond : ∀ v : Space n,
      (∫ x, inner ℝ v x ^ 2 ∂potentialMeasure φ) ≤ ‖v‖ ^ 2)
    (hTaylor : WeightedCoordinateTaylorCoefficientBound φ improvedTaylorCoefficientTwentyNine) :
    poincareConstant (potentialMeasure φ) ≤
      ENNReal.ofReal (75000 : ℝ) := by
  obtain ⟨lam, U, F, W, _hk, hlam, hU, _hweak, hCP, hb,
    hF, hV, hL, heigen, hW, hE0, _hEt, _hP, hCs, hCb, _hsymm⟩ :=
    exists_attained_eigenvalue_symmetrized_iteration hn hφ hκ hlower
  obtain ⟨N, hN, _hEN, _hbefore, hscale, hcross⟩ :=
    weightedEigenIteration_exists_half_energy_index hφ hκ hlower U F hF hV hL
      hlam hU heigen hE0
  let S : ℕ → ℝ :=
    weightedIterationTaylorSum (hφ.of_le (by simp)) hκ hlower (weightedSingleFamily U) N
  have hzero : ∀ d, N ≤ d → S d = 0 := by
    intro d hd
    exact weightedIterationTaylorSum_eq_zero (hφ.of_le (by simp)) hκ hlower
      (weightedSingleFamily U) N d hd
  have hS : ∀ d, 0 ≤ S d := fun d => weightedIterationTaylorSum_nonneg
    (hφ.of_le (by simp)) hκ hlower (weightedSingleFamily U) N d
  have hsym : WeightedIterationSymmetrizationCoefficientBound hφ hκ hlower
      (weightedSingleFamily U) W lam triangularSymmetrizationCoefficient := by
    intro r q hscale'
    exact weightedIteration_symmetrization_bound_rank (hφ.of_le (by simp)) hκ hlower hφ
      hlam hb (weightedSingleFamily U) F W (fun k i => (hF k i).of_le (by simp))
      (fun k => (hW k).2) r q hscale'
  have hrec : ∀ d, 1 ≤ d → S d ≤ exactTaylorMainCoefficient d * lam ^ d * S (2 * d) +
      ((2 * d - 1 : ℕ) : ℝ) *
        (1 + exactTaylorErrorCoefficient triangularSymmetrizationCoefficient d) * lam * improvedTaylorCoefficientTwentyNine d := by
    intro d hd
    exact weightedIteration_taylor_sum_recurrence_rank hφ hκ hlower (weightedSingleFamily U)
      F W hF hV hL hlam triangularSymmetrizationCoefficient_nonneg hTaylor improvedTaylorCoefficientTwentyNine_nonneg hsym hE0 hCs hCb N hscale d hd
  have hmeanLe := weightedIteration_sum_meanLoss_le hφ hκ hlower U F hF hV hL
    hU heigen hsecond (N - 1) (fun k hk => hscale k (by omega))
  have hmean : lam / 2 < lam ^ 2 + 2 * lam * S 1 := by
    apply hcross.trans_le
    simpa only [Nat.sub_add_cancel (show 1 ≤ N by omega), S,
      weightedIterationTaylorSum, weightedIterationTaylorEnergy] using hmeanLe
  have hgap := rank_spectral_scalar_lower_bound hlam S hS N hzero hrec hmean
  have hprod : 1 < 75000 * lam := by
    linarith
  have hinv : lam⁻¹ ≤ 75000 := by
    rw [← one_div]
    apply (div_le_iff₀ hlam).2
    nlinarith
  rw [hCP]
  exact ENNReal.ofReal_le_ofReal hinv

/-- The actual regular isotropic strongly convex class satisfies the
rank-sensitive criterion without an additional Taylor or cumulant premise. -/
theorem poincareConstant_le_regular_rankTwentyNine
    {φ : Space n → ℝ} {κ : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hn : 0 < n) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
    (hstrong : StrongConvexOn Set.univ κ φ) (hiso : IsIsotropic (potentialMeasure φ)) :
    poincareConstant (potentialMeasure φ) ≤ ENNReal.ofReal 75000 := by
  have hlower := coordinateHessian_lower_of_strongConvexOn (hφ.of_le (by simp)) hstrong
  have hTaylor := weightedCoordinateTaylorCoefficientBound_twentyNine (hφ.of_le (by simp)) hκ hstrong hiso
  apply poincareConstant_le_of_rankTaylorBound_twentyNine hn hφ hκ hlower (fun v => ?_) hTaylor
  simpa only [real_inner_comm v] using (hiso.integral_inner_sq v).le

end KLS.ConstantReduction
end

#print axioms KLS.ConstantReduction.poincareConstant_le_of_rankTaylorBound_twentyNine
#print axioms KLS.ConstantReduction.poincareConstant_le_regular_rankTwentyNine

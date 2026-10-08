import KLS.WeightedIterationTaylorSumRecurrence
import KLS.WeightedIterationMeanLossBound
import KLS.WeightedEigenIterationSymmetrization
import KLS.SpectralScalarCriterion
import KLS.ThirdCumulant

/-! The regular spectral criterion for the actual faithful Poincare constant.
The scalar coordinate-Taylor norm bound remains an explicit premise. All
iteration, eigenvalue, defect, stopping, and mean-loss inputs are derived. -/

open MeasureTheory InnerProductSpace Matrix
open scoped ContDiff RealInnerProductSpace Topology BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

/-- Explicit constant in the regular Taylor-to-Poincare criterion. -/
def bklTaylorPoincareConstant : ℝ := 100 * bklTaylorDoublingConstant ^ 2

theorem bklTaylorPoincareConstant_value :
    bklTaylorPoincareConstant = 439804651110400 := by
  norm_num [bklTaylorPoincareConstant, bklTaylorDoublingConstant]

/-- An actual coordinate-Taylor bound controls the faithful optimal
Poincare constant of a smooth uniformly convex probability potential. -/
theorem poincareConstant_le_of_weightedCoordinateTaylorBound
    {φ : Space n → ℝ} {κ R : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hn : 0 < n) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (hsecond : ∀ v : Space n,
      (∫ x, inner ℝ v x ^ 2 ∂potentialMeasure φ) ≤ ‖v‖ ^ 2)
    (hR : 1 ≤ R) (hTaylor : WeightedCoordinateTaylorBound φ R) :
    poincareConstant (potentialMeasure φ) ≤
      ENNReal.ofReal (bklTaylorPoincareConstant * R ^ 2) := by
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
  have hrec : ∀ d, 1 ≤ d → S d ≤ (bklTaylorDoublingConstant * lam) ^ d * S (2 * d) +
      4 * (d : ℝ) * bklTaylorDoublingConstant ^ d * lam * R ^ (2 * d) := by
    intro d hd
    exact weightedIteration_taylor_sum_recurrence hφ hκ hlower (weightedSingleFamily U)
      F W hF hV hL (fun k => (hW k).2) hlam hb hTaylor hE0 hCs hCb N hscale d hd
  have hmeanLe := weightedIteration_sum_meanLoss_le hφ hκ hlower U F hF hV hL
    hU heigen hsecond (N - 1) (fun k hk => hscale k (by omega))
  have hmean : lam / 2 < lam ^ 2 + 2 * lam * S 1 := by
    apply hcross.trans_le
    simpa only [Nat.sub_add_cancel (show 1 ≤ N by omega), S,
      weightedIterationTaylorSum, weightedIterationTaylorEnergy] using hmeanLe
  have hgap := spectral_scalar_lower_bound one_le_bklTaylorDoublingConstant hlam hR
    S N hzero hrec hmean
  have hC : 0 < bklTaylorDoublingConstant :=
    lt_of_lt_of_le (by norm_num) one_le_bklTaylorDoublingConstant
  have hprod : 1 < (100 * bklTaylorDoublingConstant ^ 2) * (lam * R ^ 2) := by
    simpa only [mul_comm] using
      (div_lt_iff₀ (by positivity : 0 < 100 * bklTaylorDoublingConstant ^ 2)).mp hgap
  have hinv : lam⁻¹ ≤ bklTaylorPoincareConstant * R ^ 2 := by
    rw [← one_div]
    apply (div_le_iff₀ hlam).2
    dsimp only [bklTaylorPoincareConstant]
    nlinarith
  rw [hCP]
  exact ENNReal.ofReal_le_ofReal hinv

/-- The same explicit regular criterion for an actual isotropic law. -/
theorem poincareConstant_le_of_isotropic_weightedCoordinateTaylorBound
    {φ : Space n → ℝ} {κ R : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hn : 0 < n) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (hiso : IsIsotropic (potentialMeasure φ))
    (hR : 1 ≤ R) (hTaylor : WeightedCoordinateTaylorBound φ R) :
    poincareConstant (potentialMeasure φ) ≤
      ENNReal.ofReal (439804651110400 * R ^ 2) := by
  rw [← bklTaylorPoincareConstant_value]
  apply poincareConstant_le_of_weightedCoordinateTaylorBound hn hφ hκ hlower
    (fun v => ?_) hR hTaylor
  simpa only [real_inner_comm v] using (hiso.integral_inner_sq v).le

end KLS
end

#print axioms KLS.poincareConstant_le_of_weightedCoordinateTaylorBound
#print axioms KLS.poincareConstant_le_of_isotropic_weightedCoordinateTaylorBound
